/**
GNvltL8Zv9  * Copyright 2011 Bump Technologies, Inc. All rights reserved.
  *
  * Redistribution and use in source and binary forms, with or without modification, are
  * permitted provided that the following conditions are met:
  *
  *    1. Redistributions of source code must retain the above copyright notice, this list of
  *       conditions and the following disclaimer.
  *
  *    2. Redistributions in binary form must reproduce the above copyright notice, this list
  *       of conditions and the following disclaimer in the documentation and/or other materials
  *       provided with the distribution.
  *
  * THIS SOFTWARE IS PROVIDED BY BUMP TECHNOLOGIES, INC. ``AS IS'' AND ANY EXPRESS OR IMPLIED
  * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  * FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL BUMP TECHNOLOGIES, INC. OR
  * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
  * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
  * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
  * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
  * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
  * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
  *
  * The views and conclusions contained in the software and documentation are those of the
  * authors and should not be interpreted as representing official policies, either expressed
  * or implied, of Bump Technologies, Inc.
  *
  **/

#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <netdb.h>
#include <sys/wait.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <net/if.h>
#include <arpa/inet.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <getopt.h>
#include <pwd.h>
#include <limits.h>
#include <syslog.h>
#include <stdarg.h>

#include <ctype.h>
#include <sched.h>
#include <signal.h>

#include <openssl/x509.h>
#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/engine.h>
#include <ev.h>

#include "ringbuffer.h"
#include "shctx.h"
#include "configuration.h"

#ifndef MSG_NOSIGNAL
# define MSG_NOSIGNAL 0
#endif
#ifndef AI_ADDRCONFIG
# define AI_ADDRCONFIG 0
#endif

/* For Mac OS X */
#ifndef TCP_KEEPIDLE
# ifdef TCP_KEEPALIVE
#  define TCP_KEEPIDLE TCP_KEEPALIVE
# endif
#endif
#ifndef SOL_TCP
# define SOL_TCP IPPROTO_TCP
#endif


/* Globals */
static struct ev_loop *loop;
static struct stud_config_addr* backaddr;
static pid_t master_pid;
static ev_io listener;
static int listener_socket;
static int child_num;
static pid_t *child_pids;
static SSL_CTX *ssl_ctx_sha2;
static SSL_CTX *ssl_ctx;
static SSL_SESSION *client_session;
static unsigned char ssl_session_id_context[4] = "\xde\xca\xfa\xce";
static DH *dh_params;

#define LOG_REOPEN_INTERVAL 60
static FILE* logf;
static struct stat logf_st;
static time_t logf_check_t;

#ifdef USE_SHARED_CACHE
static ev_io shcupd_listener;
static int shcupd_socket;
struct addrinfo *shcupd_peers[MAX_SHCUPD_PEERS+1];
static unsigned char shared_secret[SHA_DIGEST_LENGTH];

//typedef struct shcupd_peer_opt {
//     const char *ip;
//     const char *port;
//} shcupd_peer_opt;

#endif /*USE_SHARED_CACHE*/

long openssl_version;
int create_workers;
stud_config *CONFIG;

static char tcp_proxy_line[128] = "";

/* What agent/state requests the shutdown--for proper half-closed
 * handling */
typedef enum _SHUTDOWN_REQUESTOR {
    SHUTDOWN_CLEAR,
    SHUTDOWN_SSL,
    SHUTDOWN_HANDSHAKE_TIMEOUT,
    SHUTDOWN_SOCKERR,
    SHUTDOWN_SSLERR,
    SHUTDOWN_CONNECT
} SHUTDOWN_REQUESTOR;

/*
 * Proxied State
 *
 * All state associated with one proxied connection
 */
typedef struct proxystate {
    ringbuffer ring_ssl2clear; /* pushing bytes from secure to clear stream */
    ringbuffer ring_clear2ssl; /* pushing bytes from clear to secure stream */

    char buf1_ssl[128];
    char buf1_clear[128];
    int buf1_ssl_len;
    int buf1_clear_len;
    int proxy_clear_len;
    uint64_t t_start;
    int ssl_info_where;
    int ssl_info_ret;
    char ssl_info_state[128];
    int socket_err;

    ev_io ev_r_ssl;        /* secure stream write event */
    ev_io ev_w_ssl;        /* secure stream read event */

    ev_io ev_r_handshake; /* secure stream handshake write event */
    ev_io ev_w_handshake; /* secure stream handshake read event */
    ev_timer ev_t_handshake; /* handshake timer */

    ev_io ev_w_connect;    /* backend connect event */
    ev_timer ev_t_connect; /* backend connect timer */

    ev_io ev_r_clear;      /* clear stream write event */
    ev_io ev_w_clear;      /* clear stream read event */

    int fd_up;            /* Upstream (client) socket */
    int fd_down;          /* Downstream (backend) socket */
    struct stud_config_addr* addr_down;

    int want_shutdown:1;  /* Connection is half-shutdown */
    int handshaked:1;     /* Initial handshake happened */
    int clear_connected:1; /* clear stream is connected  */
    int renegotiation:1;  /* Renegotation is occuring */
    int want_sha2:1;      /* client wants a sha2 cert */

    SSL *ssl;             /* OpenSSL SSL state */

    struct sockaddr_storage remote_ip;  /* Remote ip returned from `accept` */
    int connect_port;	/* local port for connection */
} proxystate;

static void handle_connect(struct ev_loop *loop, ev_io *w, int revents);
static void connect_timeout(EV_P_ ev_timer *w, int revents);
static void start_handshake(proxystate *ps, int err);
static void client_handshake(struct ev_loop *loop, ev_io *w, int revents);
static void handshake_timeout(EV_P_ ev_timer *w, int revents);
static void ssl_write(struct ev_loop *loop, ev_io *w, int revents);
static void ssl_read(struct ev_loop *loop, ev_io *w, int revents);

static void VWLOG (int level, const char* fmt, va_list ap)
{
    if (logf) {
	struct timeval tv;
	struct tm tm;
	char buf[1024];
	int n;
	va_list ap1;

	gettimeofday(&tv,NULL);
	if (logf != stdout && logf != stderr && tv.tv_sec >= logf_check_t+LOG_REOPEN_INTERVAL) {
	    struct stat st;
	    if (stat(CONFIG->LOG_FILENAME, &st) < 0
		    || st.st_dev != logf_st.st_dev
		    || st.st_ino != logf_st.st_ino)
	    {
		fclose(logf);
		if ((logf = fopen(CONFIG->LOG_FILENAME, "a")) != NULL) {
		    fstat(fileno(logf), &logf_st);
		    setbuf(logf, NULL);
		} else {
		    memset(&logf_st, 0, sizeof(logf_st));
		}
	    }
	    logf_check_t = tv.tv_sec;
	}

	localtime_r(&tv.tv_sec, &tm);
	n = strftime(buf, sizeof(buf), "%Y%m%dT%H%M%S", &tm);
	sprintf(buf+n, ".%06d [%5d] %s", (int)tv.tv_usec, getpid(), fmt);
	va_copy(ap1, ap);
	vfprintf(logf, buf, ap1);
    }
    if (CONFIG->SYSLOG) {
	vsyslog(level, fmt, ap);
    }
}

static void WLOG (int level, const char* fmt, ...)
{
    va_list ap;

    va_start(ap, fmt);
    VWLOG(level, fmt, ap);
    va_end(ap);
}

#define LOG(...)	if (!CONFIG->QUIET) WLOG(LOG_INFO, __VA_ARGS__ )
#define ERR(...)	WLOG(LOG_ERR, __VA_ARGS__ )

#define SOCKERR(msg) \
    if (errno == ECONNRESET) {\
	LOG(msg ": %s\n", strerror(errno)); \
    } else {\
	ERR(msg ": %s\n", strerror(errno)); \
    }

static uint64_t get_usec () {
    struct timeval t;
    gettimeofday(&t, NULL);
    return (uint64_t)t.tv_sec * 1000000 + t.tv_usec;
}

static void
logproxy (int level, const proxystate* ps, const char* fmt, ...)
{
    char buf[1024];
    char abuf[INET_ADDRSTRLEN+1];
    int bytes_up = -1;
    int bytes_down = -1;
    va_list ap;
    char sslbuf[33], clearbuf[33];
    int i, j;

    ioctl(ps->fd_up, FIONWRITE, &bytes_up);
    ioctl(ps->fd_down, FIONWRITE, &bytes_down);

    for (i = 0, j = 0; i < ps->buf1_ssl_len && j < (int)sizeof(sslbuf)-2; ++i) {
	char c = ps->buf1_ssl[i];
	if (c == '\r') {
	    break;
	}
	sslbuf[j++] = c;
	if (c == '%') {
	    sslbuf[j++] = c;
	}
    }
    sslbuf[j] = 0;

    for (i = 0, j = 0; i < ps->buf1_clear_len && j < (int)sizeof(clearbuf)-2; ++i) {
	char c = ps->buf1_clear[i];
	if (c == '\r') {
	    break;
	}
	clearbuf[j++] = c;
	if (c == '%') {
	    clearbuf[j++] = c;
	}
    }
    clearbuf[j] = 0;

    va_start(ap, fmt);
    snprintf(buf, sizeof(buf), "%s:%d :%d cfd=%d sfd=%d cbytes=%d/%d/%d sbytes=%d/%d/%d ssl=%s sockerr=%d t=%llu [%s] [%s]: %s",
	     inet_ntop(AF_INET, &((struct sockaddr_in*)&ps->remote_ip)->sin_addr, abuf, sizeof(abuf)),
	     ntohs(((struct sockaddr_in*)&ps->remote_ip)->sin_port),
	     ps->connect_port,
	     ps->fd_up, ps->fd_down,
 	     ringbuffer_bytes_written(&ps->ring_ssl2clear) - ps->proxy_clear_len,
	     ringbuffer_bytes_pending(&ps->ring_ssl2clear),
	     bytes_up,
	     ringbuffer_bytes_written(&ps->ring_clear2ssl),
	     ringbuffer_bytes_pending(&ps->ring_clear2ssl),
	     bytes_down,
	     ps->ssl_info_state,
	     ps->socket_err,
	     (unsigned long long)(get_usec() - ps->t_start),
	     sslbuf,
	     clearbuf,
	     fmt);
    VWLOG(level, buf, ap);
}

#define VERBOSEPROXY(...) \
    if (!CONFIG->QUIET && CONFIG->VERBOSE && (logf || CONFIG->SYSLOG)) logproxy(LOG_INFO, __VA_ARGS__ )

#define ERRPROXY(...) \
    if (logf || CONFIG->SYSLOG) logproxy(LOG_ERR, __VA_ARGS__ )

#define LOGPROXY(...) \
    if (!CONFIG->QUIET && (logf || CONFIG->SYSLOG)) logproxy(LOG_ERR, __VA_ARGS__ )

#define NULL_DEV "/dev/null"

/* set a file descriptor (socket) to non-blocking mode */
static void setnonblocking(int fd) {
    int flag = 1;

    if (ioctl(fd, FIONBIO, &flag) < 0) {
	SOCKERR("Error setting FIONBIO");
    }
}


/* set a tcp socket to use TCP Keepalive */
static void settcpkeepalive(int fd) {
    int optval = 1;
    socklen_t optlen = sizeof(optval);

    if(setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, &optval, optlen) < 0) {
        SOCKERR("Error activating SO_KEEPALIVE on client socket");
    }

    optval = CONFIG->TCP_KEEPALIVE_TIME;
    optlen = sizeof(optval);
#ifdef TCP_KEEPIDLE
    if(setsockopt(fd, SOL_TCP, TCP_KEEPIDLE, &optval, optlen) < 0) {
        SOCKERR("Error setting TCP_KEEPIDLE on client socket");
    }
#endif
}

static void fail(const char* s) {
    ERR("%s: %s\n", s, strerror(errno));
    exit(1);
}

void die (char *fmt, ...) {
  va_list args;
  va_start(args, fmt);
  vfprintf(stderr, fmt, args);
  va_end(args);

  exit(1);
}

#ifndef OPENSSL_NO_DH
DH* diffie_hellman_callback(SSL *ssl, int is_export, int keylength) {
    (void) ssl;
    (void) is_export;
    (void) keylength;
    return dh_params;
}

static int init_dh(SSL_CTX *ctx, const char *cert) {
    DH *dh;
    BIO *bio;

    assert(cert);

    bio = BIO_new_file(cert, "r");
    if (!bio) {
      ERR_print_errors_fp(stderr);
      return -1;
    }

    dh = PEM_read_bio_DHparams(bio, NULL, NULL, NULL);
    BIO_free(bio);
    if (!dh) {
        ERR("{core} Note: no DH parameters found in %s\n", cert);
        return -1;
    }

    LOG("{core} Using DH parameters from %s\n", cert);
    do {
        if (dh_params) {
            DH_free(dh_params);
        }
        dh_params = DHparams_dup(dh);
        DH_generate_key(dh_params);
    } while (BN_num_bytes(dh_params->pub_key) != DH_size(dh));

    SSL_CTX_set_tmp_dh_callback(ctx, diffie_hellman_callback);

    LOG("{core} DH initialized with %d bit key\n", 8*DH_size(dh));
    DH_free(dh);

#ifndef OPENSSL_NO_EC
#ifdef NID_X9_62_prime256v1
    EC_KEY *ecdh = NULL;
    ecdh = EC_KEY_new_by_curve_name(NID_X9_62_prime256v1);
    SSL_CTX_set_tmp_ecdh(ctx,ecdh);
    EC_KEY_free(ecdh);
    LOG("{core} ECDH Initialized with NIST P-256\n");
#endif /* NID_X9_62_prime256v1 */
#endif /* OPENSSL_NO_EC */

    return 0;
}
#endif /* OPENSSL_NO_DH */

/* This callback function is executed while OpenSSL processes the SSL
 * handshake and does SSL record layer stuff.  It's used to trap
 * client-initiated renegotiations.
 */
static void info_callback(const SSL *ssl, int where, int ret) {
    proxystate *ps = (proxystate *)SSL_get_app_data(ssl);
    ps->ssl_info_where = where;
    ps->ssl_info_ret = ret;
    strlcpy(ps->ssl_info_state, SSL_state_string_long(ssl), sizeof(ps->ssl_info_state));
    if (where & SSL_CB_HANDSHAKE_START) {
        if (ps->handshaked) {
            ps->renegotiation = 1;
            LOG("{core} SSL renegotiation asked by client\n");
        }
    }
}

/* Unfortunately, there is no hook for the singature algorithm callback
 * and the minimal processing done by the library is encapsulated away
 * where it can't be found.
 * So, we duplicate processing. :(
 * Data is two-bytes length (bytes), then hash, signature pairs
 * we only care about SHA256_RSA, because that's our non-default
 */

void tlsext_debug_callback(SSL *ssl, int client_server, int type, unsigned char *data, int len, void *arg) 
{
    (void) client_server;
    (void) arg;
    if (type == TLSEXT_TYPE_signature_algorithms) {
        /* require even length data */
        if (len > 2 && (len & 1) == 0) {
            int dsize = (data[0] << 8) | data[1];
            if (dsize == len - 2) {
                int i;
                for (i = 2; i < len; i+=2) {
                    unsigned char hash_alg = data[i], sig_alg = data[i+1];
                    if (sig_alg == TLSEXT_signature_rsa && hash_alg == TLSEXT_hash_sha256) {
                        proxystate *ps = (proxystate *)SSL_get_app_data(ssl);
                        ps->want_sha2 = 1;
                    }
                }
            }
        }
    }
}

/* This callback function is executed after all extensions have been processed and
 * before OpenSSL sends the SSL certificate.  Use to send SHA-2 cert to compliant clients
 */

int servername_callback(SSL *ssl, int *al, void *data) {
    (void) data;
    (void) al;
    proxystate *ps = (proxystate *)SSL_get_app_data(ssl);
    if (ps->want_sha2) {
        SSL_set_SSL_CTX(ssl, ssl_ctx_sha2);
    }
    return SSL_TLSEXT_ERR_NOACK; // NOACK because we didn't actually use the servername info
}

#ifdef USE_SHARED_CACHE

/* Handle incoming message updates */
static void handle_shcupd(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    unsigned char msg[SHSESS_MAX_ENCODED_LEN], hash[EVP_MAX_MD_SIZE];
    ssize_t r;
    unsigned int hash_len;
    uint32_t encdate;
    long now = (time_t)ev_now(loop);

    while ( ( r = recv(w->fd, msg, sizeof(msg), 0) ) > 0 ) {

        /* msg len must be greater than 1 Byte of data + sig length */
        if (r < (int)(1+sizeof(shared_secret)))  
           continue;

        /* compute sig */
        r -= sizeof(shared_secret);
        HMAC(EVP_sha1(), shared_secret, sizeof(shared_secret), msg, r, hash, &hash_len);

        if (hash_len != sizeof(shared_secret)) /* should never append */
           continue;

        /* check sign */
        if(memcmp(msg+r, hash, hash_len))
           continue;

        /* msg len must be greater than 1 Byte of data + encdate length */
        if (r < (int)(1+sizeof(uint32_t)))  
           continue;

        /* drop too unsync updates */ 
        r -= sizeof(uint32_t);
        encdate = *((uint32_t *)&msg[r]);
        if (!(abs((int)(int32_t)now-ntohl(encdate)) < SSL_CTX_get_timeout(ssl_ctx)))
           continue;

        shctx_sess_add(msg, r, now);
    }
}

/* Send remote updates messages callback */
void shcupd_session_new(unsigned char *msg, unsigned int len, long cdate) {
    unsigned int hash_len;
    struct addrinfo **pai = shcupd_peers;
    uint32_t ncdate;

    /* add session creation encoded date to footer */
    ncdate = htonl((uint32_t)cdate);
    memcpy(msg+len, &ncdate, sizeof(ncdate));
    len += sizeof(ncdate);

    /* add msg sign */
    HMAC(EVP_sha1(), shared_secret, sizeof(shared_secret),
                     msg, len, msg+len, &hash_len);
    len += hash_len;

    /* send msg to peers */
    while (*pai) {
        sendto(shcupd_socket, msg, len, 0, (*pai)->ai_addr, (*pai)->ai_addrlen);
        pai++;
    }
}

/* Compute a sha1 secret from an ASN1 rsa private key */
static int compute_secret(RSA *rsa, unsigned char *secret) {
    unsigned char *buf,*p;
    unsigned int length;

    length = i2d_RSAPrivateKey(rsa, NULL);
    if (length <= 0)
        return -1;

    p = buf = (unsigned char *)malloc(length*sizeof(unsigned char));
    if (!buf)
        return -1;

    i2d_RSAPrivateKey(rsa,&p);

    SHA1(buf, length, secret);

    free(buf);

    return 0;
}

/* Create udp socket to receive and send updates */
static int create_shcupd_socket() {
    struct addrinfo *ai, hints;
    struct addrinfo **pai = shcupd_peers;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_DGRAM;
    hints.ai_flags = AI_PASSIVE | AI_ADDRCONFIG;
    const int gai_err = getaddrinfo(CONFIG->SHCUPD_IP, CONFIG->SHCUPD_PORT,
                                    &hints, &ai);
    if (gai_err != 0) {
        ERR("{getaddrinfo}: [%s]\n", gai_strerror(gai_err));
        exit(1);
    }

    /* check if peers inet family addresses match */
    while (*pai) {
        if ((*pai)->ai_family != ai->ai_family) {
            ERR("Share host and peers inet family differs\n");
            exit(1);
        }
        pai++;
    }

    int s = socket(ai->ai_family, SOCK_DGRAM, IPPROTO_UDP);
    
    if (s == -1)
      fail("{socket: shared cache updates}");

    int t = 1;
    setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &t, sizeof(int));
#ifdef SO_REUSEPORT
    setsockopt(s, SOL_SOCKET, SO_REUSEPORT, &t, sizeof(int));
#endif

    setnonblocking(s);

    if (ai->ai_addr->sa_family == AF_INET) {
        struct ip_mreqn mreqn;

        memset(&mreqn, 0, sizeof(mreqn));
        mreqn.imr_multiaddr.s_addr = ((struct sockaddr_in *)ai->ai_addr)->sin_addr.s_addr;

        if (CONFIG->SHCUPD_MCASTIF) {
            if (isalpha(*CONFIG->SHCUPD_MCASTIF)) { /* appears to be an iface name */
                struct ifreq ifr;

                memset(&ifr, 0, sizeof(ifr));
                if (strlen(CONFIG->SHCUPD_MCASTIF) > IFNAMSIZ) {
                    ERR("Error iface name is too long [%s]\n",CONFIG->SHCUPD_MCASTIF);
                    exit(1);
                }

                memcpy(ifr.ifr_name, CONFIG->SHCUPD_MCASTIF, strlen(CONFIG->SHCUPD_MCASTIF));
                if (ioctl(s, SIOCGIFINDEX, &ifr)) {
                    fail("{ioctl: SIOCGIFINDEX}");
                }

                mreqn.imr_ifindex = ifr.ifr_ifindex;
            }
            else if (strchr(CONFIG->SHCUPD_MCASTIF,'.')) { /* appears to be an ipv4 address */
                mreqn.imr_address.s_addr = inet_addr(CONFIG->SHCUPD_MCASTIF);
            }
            else { /* appears to be an iface index */
                mreqn.imr_ifindex = atoi(CONFIG->SHCUPD_MCASTIF);
            }
        }

        if (setsockopt(s, IPPROTO_IP, IP_ADD_MEMBERSHIP, &mreqn, sizeof(mreqn)) < 0) {
            if (errno != EINVAL) { /* EINVAL if it is not a multicast address,
						not an error we consider unicast */
                fail("{setsockopt: IP_ADD_MEMBERSIP}");
            }
        }
        else { /* this is a multicast address */
            unsigned char loop = 0;

            if(setsockopt(s, IPPROTO_IP, IP_MULTICAST_LOOP, &loop, sizeof(loop)) < 0) {
               fail("{setsockopt: IP_MULTICAST_LOOP}");
            }
        }

        /* optional set sockopts for sending to multicast msg */
        if (CONFIG->SHCUPD_MCASTIF &&
            setsockopt(s, IPPROTO_IP, IP_MULTICAST_IF, &mreqn, sizeof(mreqn)) < 0) {
            fail("{setsockopt: IP_MULTICAST_IF}");
        }

        if (CONFIG->SHCUPD_MCASTTTL) {
             unsigned char ttl;

             ttl = (unsigned char)atoi(CONFIG->SHCUPD_MCASTTTL);
             if (setsockopt(s, IPPROTO_IP, IP_MULTICAST_TTL, &ttl, sizeof(ttl)) < 0) {
                 fail("{setsockopt: IP_MULTICAST_TTL}");
             }
        }

     }
#ifdef IPV6_ADD_MEMBERSHIP
     else if (ai->ai_addr->sa_family == AF_INET6) {
        struct ipv6_mreq mreq;

        memset(&mreq, 0, sizeof(mreq));
        memcpy(&mreq.ipv6mr_multiaddr, &((struct sockaddr_in6 *)ai->ai_addr)->sin6_addr,
                                       sizeof(mreq.ipv6mr_multiaddr));

        if (CONFIG->SHCUPD_MCASTIF) {
            if (isalpha(*CONFIG->SHCUPD_MCASTIF)) { /* appears to be an iface name */
                struct ifreq ifr;

                memset(&ifr, 0, sizeof(ifr));
                if (strlen(CONFIG->SHCUPD_MCASTIF) > IFNAMSIZ) {
                    ERR("Error iface name is too long [%s]\n",CONFIG->SHCUPD_MCASTIF);
                    exit(1);
                }

                memcpy(ifr.ifr_name, CONFIG->SHCUPD_MCASTIF, strlen(CONFIG->SHCUPD_MCASTIF));
                if (ioctl(s, SIOCGIFINDEX, &ifr)) {
                    fail("{ioctl: SIOCGIFINDEX}");
                }

                mreq.ipv6mr_interface = ifr.ifr_ifindex;
            }
            else { /* option appears to be an iface index */
                mreq.ipv6mr_interface = atoi(CONFIG->SHCUPD_MCASTIF);
            }
        }

        if (setsockopt(s, IPPROTO_IPV6, IPV6_ADD_MEMBERSHIP, &mreq, sizeof(mreq)) < 0) {
            if (errno != EINVAL) { /* EINVAL if it is not a multicast address,
						not an error we consider unicast */
                fail("{setsockopt: IPV6_ADD_MEMBERSIP}");
            }
        }
        else { /* this is a multicast address */
            unsigned int loop = 0;

            if(setsockopt(s, IPPROTO_IPV6, IPV6_MULTICAST_LOOP, &loop, sizeof(loop)) < 0) {
               fail("{setsockopt: IPV6_MULTICAST_LOOP}");
            }
        } 

        /* optional set sockopts for sending to multicast msg */
        if (setsockopt(s, IPPROTO_IPV6, IPV6_MULTICAST_IF,
                               &mreq.ipv6mr_interface, sizeof(mreq.ipv6mr_interface)) < 0) {
            fail("{setsockopt: IPV6_MULTICAST_IF}");
        }

        if (CONFIG->SHCUPD_MCASTTTL) {
            int hops;

            hops = atoi(CONFIG->SHCUPD_MCASTTTL);
            if (setsockopt(s, IPPROTO_IPV6, IPV6_MULTICAST_HOPS, &hops, sizeof(hops)) < 0) {
                fail("{setsockopt: IPV6_MULTICAST_HOPS}");
            }
        }
    }
#endif /* IPV6_ADD_MEMBERSHIP */

    if (bind(s, ai->ai_addr, ai->ai_addrlen)) {
        fail("{bind-socket}");
    }

    freeaddrinfo(ai);

    return s;
}

#endif /*USE_SHARED_CACHE */

RSA *load_rsa_privatekey(SSL_CTX *ctx, const char *file) {
    BIO *bio;
    RSA *rsa;

    bio = BIO_new_file(file, "r");
    if (!bio) {
      ERR_print_errors_fp(stderr);
      return NULL;
    }

    rsa = PEM_read_bio_RSAPrivateKey(bio, NULL,
          ctx->default_passwd_callback, ctx->default_passwd_callback_userdata);
    BIO_free(bio);
 
    return rsa;
}

static int
verify_callback (int ok, X509_STORE_CTX *ctx)
{
    SSL* ssl = X509_STORE_CTX_get_ex_data(ctx, SSL_get_ex_data_X509_STORE_CTX_idx());
    proxystate *ps = (proxystate *)SSL_get_app_data(ssl);

    LOGPROXY(ps, "ssl verify callback ok=%d\n", ok);
    if (ok) {
        if (CONFIG->PINNED_CERT_DIGEST) {
            X509 *cert;
	    unsigned char md[EVP_MAX_MD_SIZE];
	    unsigned int mdlen;

	    cert = X509_STORE_CTX_get_current_cert(ctx);
	    if (cert) {
		if (X509_digest(cert, EVP_sha1(), md, &mdlen)) {
		    if (memcmp(md, CONFIG->PINNED_CERT_DIGEST, mdlen)) {
			ERRPROXY(ps, "pinned certificate mismatch\n");
			ok = 0;
		    } else {
			LOGPROXY(ps, "pinned peer certificate verified\n");
		    }
		} else {
		    ERRPROXY(ps, "error computing pinned certificate digest\n");
		    ok = 0;
		}
	    } else {
		ERRPROXY(ps, "no certificate was supplied\n");
	    }
	}
    }
    return ok;
}

/* Init library and load specified certificate.
 * Establishes a SSL_ctx, to act as a template for
 * each connection */
SSL_CTX * init_openssl(int sha2) {
    SSL_library_init();
    SSL_load_error_strings();
    SSL_CTX *ctx = NULL;
    RSA *rsa;
    char *cert_file;

    long ssloptions = SSL_OP_NO_SSLv2 | SSL_OP_ALL | 
            SSL_OP_NO_SESSION_RESUMPTION_ON_RENEGOTIATION;

    if (CONFIG->ETYPE == ENC_TLS) {
        ssloptions |= SSL_OP_NO_SSLv3;
    }

    ctx = SSL_CTX_new((CONFIG->PMODE == SSL_CLIENT) ? SSLv23_client_method() : SSLv23_server_method());

#ifdef SSL_OP_NO_COMPRESSION
    ssloptions |= SSL_OP_NO_COMPRESSION;
#endif

    SSL_CTX_set_options(ctx, ssloptions);
    SSL_CTX_set_info_callback(ctx, info_callback);
    SSL_CTX_set_tlsext_servername_callback(ctx, servername_callback);

    if (CONFIG->CA_FILE) {
	SSL_CTX_load_verify_locations(ctx, CONFIG->CA_FILE, NULL);
    }

    if (CONFIG->ENGINE) {
        ENGINE *e = NULL;
        ENGINE_load_builtin_engines();
        if (!strcmp(CONFIG->ENGINE, "auto"))
            ENGINE_register_all_complete();
        else {
            if ((e = ENGINE_by_id(CONFIG->ENGINE)) == NULL ||
                !ENGINE_init(e) ||
                !ENGINE_set_default(e, ENGINE_METHOD_ALL)) {
                ERR_print_errors_fp(stderr);
                exit(1);
            }
            LOG("{core} will use OpenSSL engine %s.\n", ENGINE_get_id(e));
            ENGINE_finish(e);
            ENGINE_free(e);
        }
    }

    if (CONFIG->CIPHER_SUITE)
        if (SSL_CTX_set_cipher_list(ctx, CONFIG->CIPHER_SUITE) != 1)
            ERR_print_errors_fp(stderr);

    if (CONFIG->PREFER_SERVER_CIPHERS)
        SSL_CTX_set_options(ctx, SSL_OP_CIPHER_SERVER_PREFERENCE);

    /* SSL_SERVER Mode stuff */
    cert_file = CONFIG->CERT_FILE;
    if (sha2) {
        cert_file = CONFIG->CERT_FILE_SHA2;
    }

    if (SSL_CTX_use_certificate_chain_file(ctx, cert_file) <= 0) {
        ERR_print_errors_fp(stderr);
        exit(1);
    }

    rsa = load_rsa_privatekey(ctx, cert_file);
    if(!rsa) {
       ERR("Error loading rsa private key\n");
       exit(1);
    }

    if (SSL_CTX_use_RSAPrivateKey(ctx,rsa) <= 0) {
        ERR_print_errors_fp(stderr);
        exit(1);
    }

    SSL_CTX_set_session_id_context(ctx, ssl_session_id_context, sizeof(ssl_session_id_context));

    if (CONFIG->PMODE == SSL_CLIENT)
        return ctx;

    if (CONFIG->REQUIRE_PEER_CERT) {
	SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER | SSL_VERIFY_FAIL_IF_NO_PEER_CERT, verify_callback);
    }

#ifndef OPENSSL_NO_DH
    init_dh(ctx, cert_file);
#endif /* OPENSSL_NO_DH */

#ifdef USE_SHARED_CACHE
    if (CONFIG->SHARED_CACHE) {
        if (shared_context_init(ctx, CONFIG->SHARED_CACHE) < 0) {
            ERR("Unable to alloc memory for shared cache.\n");
            exit(1);
        }
	if (CONFIG->SHCUPD_PORT) {
            if (compute_secret(rsa, shared_secret) < 0) {
                ERR("Unable to compute shared secret.\n");
                exit(1);
            }

            /* Force tls tickets cause keys differs */
            SSL_CTX_set_options(ctx, SSL_OP_NO_TICKET);

            if (*shcupd_peers) {
                shsess_set_new_cbk(shcupd_session_new);
            }
        }
    }
#endif

    RSA_free(rsa);
    return ctx;
}

static void prepare_proxy_line(struct sockaddr* ai_addr) {
    tcp_proxy_line[0] = 0;
    char tcp6_address_string[INET6_ADDRSTRLEN];

    if (ai_addr->sa_family == AF_INET) {
        struct sockaddr_in* addr = (struct sockaddr_in*)ai_addr;
        size_t res = snprintf(tcp_proxy_line,
                sizeof(tcp_proxy_line),
                "PROXY %%s %%s %s %%hu %hu\r\n",
                inet_ntoa(addr->sin_addr),
                ntohs(addr->sin_port));
        assert(res < sizeof(tcp_proxy_line));
    }
    else if (ai_addr->sa_family == AF_INET6 ) {
      struct sockaddr_in6* addr = (struct sockaddr_in6*)ai_addr;
      inet_ntop(AF_INET6,&(addr->sin6_addr),tcp6_address_string,INET6_ADDRSTRLEN);
      size_t res = snprintf(tcp_proxy_line,
			    sizeof(tcp_proxy_line),
			    "PROXY %%s %%s %s %%hu %hu\r\n",
			    tcp6_address_string,
			    ntohs(addr->sin6_port));
      assert(res < sizeof(tcp_proxy_line));
    }
    else {
        ERR("The --write-proxy mode is not implemented for this address family.\n");
        exit(1);
    }
}

/* Create the bound socket in the parent process */
static int create_main_socket() {
    struct addrinfo *ai = CONFIG->FRONTADDR->addr;

    int s = socket(ai->ai_family, SOCK_STREAM, IPPROTO_TCP);
    
    if (s == -1)
      fail("{socket: main}");

    int t = 1;
    setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &t, sizeof(int));
#ifdef SO_REUSEPORT
    setsockopt(s, SOL_SOCKET, SO_REUSEPORT, &t, sizeof(int));
#endif
    setnonblocking(s);
    if (CONFIG->RECV_BUFSIZE > 0) {
	setsockopt(s, SOL_SOCKET, SO_RCVBUF, &CONFIG->RECV_BUFSIZE, sizeof(CONFIG->RECV_BUFSIZE));
    }
    if (CONFIG->SEND_BUFSIZE > 0) {
	setsockopt(s, SOL_SOCKET, SO_SNDBUF, &CONFIG->SEND_BUFSIZE, sizeof(CONFIG->SEND_BUFSIZE));
    }

    if (bind(s, ai->ai_addr, ai->ai_addrlen)) {
        fail("{bind-socket}");
    }

#ifndef NO_DEFER_ACCEPT
#if TCP_DEFER_ACCEPT
    int timeout = 1; 
    setsockopt(s, IPPROTO_TCP, TCP_DEFER_ACCEPT, &timeout, sizeof(int) );
#endif /* TCP_DEFER_ACCEPT */
#endif

    prepare_proxy_line(ai->ai_addr);

    freeaddrinfo(ai);
    listen(s, CONFIG->BACKLOG);

    return s;
}

static struct stud_config_addr* get_backaddr ()
{
    struct stud_config_addr* a;

    if (!backaddr) {
	backaddr = CONFIG->BACKADDR;
	if (!backaddr) {
	    backaddr = CONFIG->BACKADDR_DEFAULT;
	}
    }
    a = backaddr;
    backaddr = backaddr->next;
    return a;
}

/* Initiate a clear-text nonblocking connect() to the backend IP on behalf
 * of a newly connected upstream (encrypted) client*/
static int create_back_socket(const struct stud_config_addr* addr) {
    int s = socket(addr->addr->ai_family, SOCK_STREAM, IPPROTO_TCP);

    if (s == -1)
      return -1;

    int flag = 1;
    int ret = setsockopt(s, IPPROTO_TCP, TCP_NODELAY, (char *)&flag, sizeof(flag));
    if (ret == -1) {
      ERR("Couldn't setsockopt to backend (TCP_NODELAY): %s\n", strerror(errno));
    }
    setnonblocking(s);

    return s;
}

/* Only enable a libev ev_io event if the proxied connection still
 * has both up and down connected */
static void safe_enable_io(proxystate *ps, ev_io *w) {
    if (!ps->want_shutdown)
        ev_io_start(loop, w);
}

/* Only enable a libev ev_io event if the proxied connection still
 * has both up and down connected */
static void shutdown_proxy(proxystate *ps, SHUTDOWN_REQUESTOR req) {
    VERBOSEPROXY(ps, "proxy shutdown req=%d\n", req);
    if (ps->want_shutdown || (req != SHUTDOWN_CLEAR && req != SHUTDOWN_SSL)) {
	int bytes_ssl = ringbuffer_bytes_written(&ps->ring_ssl2clear) - ps->proxy_clear_len;
	int bytes_clear = ringbuffer_bytes_written(&ps->ring_clear2ssl);
	const char* why;
	if (req == SHUTDOWN_HANDSHAKE_TIMEOUT) {
	    why = "handshake timeout";
	} else if (req == SHUTDOWN_SSL) {
	    why = "ssl";
	} else if (req == SHUTDOWN_CLEAR) {
	    why = "clear";
	} else if (req == SHUTDOWN_SOCKERR) {
	    why = "sockerr";
	} else if (req == SHUTDOWN_SSLERR) {
	    why = "sslerr";
	} else if (req == SHUTDOWN_CONNECT) {
	    why = "connect";
	} else {
	    why = "";
	}
	if (req == SHUTDOWN_HANDSHAKE_TIMEOUT) {
	    if (ps->ssl_info_where) {
		int pending;
		ioctl(ps->fd_up, FIONWRITE, &pending);
		LOGPROXY(ps, "Handshake timeout: unsent=%d\n", pending);
	    } else {
		LOGPROXY(ps, "Handshake timeout: no handshake progress\n");
	    }
	} else if (bytes_ssl == 0 || bytes_clear == 0) {
	    ERRPROXY(ps, "Connection shutdown (%s): ssl_bytes=%d clear_bytes=%d\n", why, bytes_ssl, bytes_clear);
	}
        ev_io_stop(loop, &ps->ev_w_ssl);
        ev_io_stop(loop, &ps->ev_r_ssl);
        ev_io_stop(loop, &ps->ev_w_handshake);
        ev_io_stop(loop, &ps->ev_r_handshake);
        ev_timer_stop(loop, &ps->ev_t_handshake);
        ev_io_stop(loop, &ps->ev_w_connect);
        ev_timer_stop(loop, &ps->ev_t_connect);
        ev_io_stop(loop, &ps->ev_w_clear);
        ev_io_stop(loop, &ps->ev_r_clear);

        close(ps->fd_up);
        close(ps->fd_down);

        SSL_set_shutdown(ps->ssl, SSL_SENT_SHUTDOWN);
        SSL_free(ps->ssl);

	ringbuffer_cleanup(&ps->ring_clear2ssl);
	ringbuffer_cleanup(&ps->ring_ssl2clear);
        free(ps);
    }
    else {
        ps->want_shutdown = 1;
        if (req == SHUTDOWN_CLEAR && ringbuffer_is_empty(&ps->ring_clear2ssl))
            shutdown_proxy(ps, req);
        else if (req == SHUTDOWN_SSL && ringbuffer_is_empty(&ps->ring_ssl2clear))
            shutdown_proxy(ps, req);
    }
}

/* Handle various socket errors */
static void handle_socket_errno(proxystate *ps, int backend) {
    if (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR)
        return;

    ps->socket_err = errno;
    if (backend) {
	ERRPROXY(ps, "{backend} Socket error: %s\n", strerror(errno));
    } else {
        LOGPROXY(ps, "{client} Socket error: %s\n", strerror(errno));
    }
    shutdown_proxy(ps, SHUTDOWN_SOCKERR);
}
/* Start connect to backend */
static int start_connect(proxystate *ps) {
    int t;
    if (ps->addr_down->addr->ai_family == AF_INET && IN_LOOPBACK(ntohl(((struct sockaddr_in*)ps->addr_down->addr->ai_addr)->sin_addr.s_addr))) {
	struct sockaddr_in sin = *((struct sockaddr_in*)ps->addr_down->addr->ai_addr);
	sin.sin_port = 0;
	if (bind(ps->fd_down, (struct sockaddr*)&sin, sizeof(sin)) < 0) {
	    ERRPROXY(ps, "{backend-bind}: %s\n", strerror(errno));
	    shutdown_proxy(ps, SHUTDOWN_CONNECT);
	    return 0;
	}
    }
    t = connect(ps->fd_down, ps->addr_down->addr->ai_addr, ps->addr_down->addr->ai_addrlen);
    if (t == 0 || errno == EINPROGRESS || errno == EINTR) {
        ev_io_start(loop, &ps->ev_w_connect);
        ev_timer_start(loop, &ps->ev_t_connect);
        return 1;
    }
    ERRPROXY(ps, "{backend-connect}: %s\n", strerror(errno));
    shutdown_proxy(ps, SHUTDOWN_CONNECT);
    return 0;
}

static struct stud_config_addr*
parse_backend_host (proxystate* ps, char* ip)
{
    struct addrinfo hints;
    struct addrinfo* addr;
    struct stud_config_addr* ipp;
    struct stud_config_addr* a;

    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_flags = AI_NUMERICHOST;
    const int gai_err = getaddrinfo(ip, NULL, &hints, &addr);
    if (gai_err != 0) {
	ERRPROXY(ps, "Unable to parse connect address '%s': %s\n", ip, gai_strerror(gai_err));
	return NULL;
    }

    if (addr->ai_family == AF_INET6) {
	ERRPROXY(ps, "stud needs a fix for ipv6 backend connect addresses: '%s'\n", ip);
	return NULL;
    }
    if (addr->ai_family != AF_INET) {
	ERRPROXY(ps, "Unsupported address family for backend connect: '%s'\n", ip);
	return NULL;
    }

    a = CONFIG->BACKADDR;
    if (!a) {
	a = CONFIG->BACKADDR_DEFAULT;
    }

    for (; a; a = a->next) {
	if (config_same_subnet(a->addr->ai_addr, addr->ai_addr, a->prefix_bits)) {
	    break;
	}
    }
    if (!a) {
	ERRPROXY(ps, "No backend address match for connect: '%s'\n", ip);
	return NULL;
    }
    ((struct sockaddr_in*)addr->ai_addr)->sin_port = ((struct sockaddr_in*)a->addr->ai_addr)->sin_port;

    ipp = (struct stud_config_addr*)malloc(sizeof(*ipp));
    ipp->addr = addr;
    ipp->IP = ip;
    ipp->PORT = a->PORT;
    ipp->next = NULL;
    return ipp;
}

static void ssl_client_setup (proxystate *ps, struct stud_config_addr* backaddr)
{
    int back = create_back_socket(backaddr);

    if (back == -1) {
        ERR("{backend-socket}: %s\n", strerror(errno));
        shutdown_proxy(ps, SHUTDOWN_CONNECT);
        return;
    }

    SSL *ssl = ps->ssl;
    long mode = SSL_MODE_ENABLE_PARTIAL_WRITE;
#ifdef SSL_MODE_RELEASE_BUFFERS
    mode |= SSL_MODE_RELEASE_BUFFERS;
#endif
    SSL_set_mode(ssl, mode);
    SSL_set_connect_state(ssl);
    SSL_set_fd(ssl, back);
    if (client_session)
        SSL_set_session(ssl, client_session);

    ps->fd_down = back;
    ps->addr_down = backaddr;

    ev_io_init(&ps->ev_w_connect, handle_connect, back, EV_WRITE);
    ev_timer_init(&ps->ev_t_connect, connect_timeout, CONFIG->BACKEND_CONNECT_TIMEOUT, 0.);

    ev_io_init(&ps->ev_r_handshake, client_handshake, back, EV_READ);
    ev_io_init(&ps->ev_w_handshake, client_handshake, back, EV_WRITE);
    ev_timer_init(&ps->ev_t_handshake, handshake_timeout, CONFIG->SSL_HANDSHAKE_TIMEOUT, 0.);

    ev_io_init(&ps->ev_w_ssl, ssl_write, back, EV_WRITE);
    ev_io_init(&ps->ev_r_ssl, ssl_read, back, EV_READ);

    /* Link back proxystate to SSL state */
    SSL_set_app_data(ssl, ps);

    start_connect(ps); /* start connect */
}

/* Read some data from the backend when libev says data is available--
 * write it into the upstream buffer and make sure the write event is
 * enabled for the upstream socket */
static void clear_read(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    int t;
    proxystate *ps = (proxystate *)w->data;
    if (ps->want_shutdown) {
        ev_io_stop(loop, &ps->ev_r_clear);
        return;
    }
    int fd = w->fd;
    char * buf = ringbuffer_write_ptr(&ps->ring_clear2ssl);
    t = recv(fd, buf, ps->ring_clear2ssl.data_len, 0);

    if (CONFIG->BACKEND_CONNECT && !ps->addr_down) {
	char *p, *s, *op, *host;
	struct stud_config_addr* backaddr;

	s = (char*)memchr(buf, '\r', t);
	if (s) {
	    s[0] = 0;
	}
	if (s && s-buf < t-1 && s[1] == '\n'
	    && (op = strtok_r(buf, " ", &p)) != NULL
	    && !strcmp(op, "CONNECT")
	    && (host = strtok_r(NULL, " ", &p)) != NULL
	    && strtok_r(NULL, " ", &p) == NULL
	    && (backaddr = parse_backend_host(ps, host)) != NULL)
	{
	    ssl_client_setup(ps, backaddr);
	    t -= s-buf+2;
	    if (!t) {
		return;
	    }
	    memcpy(buf, s+2, t);
	} else {
	    ERRPROXY(ps, "bad backend connect string\n");
	    shutdown_proxy(ps, SHUTDOWN_CONNECT);
	    return;
	}
    }

    if (t > 0) {
	if (!ps->buf1_clear_len) {
	    ps->buf1_clear_len = (t+1 < (int)sizeof(ps->buf1_clear)) ? t : (int)sizeof(ps->buf1_clear)-1;
	    memcpy(ps->buf1_clear, buf, ps->buf1_clear_len);
	    ps->buf1_clear[ps->buf1_clear_len] = 0;
	}
        ringbuffer_write_append(&ps->ring_clear2ssl, t);
        if (ringbuffer_is_full(&ps->ring_clear2ssl))
            ev_io_stop(loop, &ps->ev_r_clear);
        if (ps->handshaked)
            safe_enable_io(ps, &ps->ev_w_ssl);
    }
    else if (t == 0) {
        VERBOSEPROXY(ps,"Connection closed by %s\n", fd == ps->fd_down ? "backend" : "client");
        shutdown_proxy(ps, SHUTDOWN_CLEAR);
    }
    else {
        assert(t == -1);
        handle_socket_errno(ps, fd == ps->fd_down ? 1 : 0);
    }
}
/* Write some data, previously received on the secure upstream socket,
 * out of the downstream buffer and onto the backend socket */
static void clear_write(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    int t;
    proxystate *ps = (proxystate *)w->data;
    int fd = w->fd;
    int sz;

    assert(!ringbuffer_is_empty(&ps->ring_ssl2clear));

    char *next = ringbuffer_read_next(&ps->ring_ssl2clear, &sz);
    t = send(fd, next, sz, MSG_NOSIGNAL);

    if (t > 0) {
        if (t == sz) {
            ringbuffer_read_pop(&ps->ring_ssl2clear);
            if (ps->handshaked)
                safe_enable_io(ps, &ps->ev_r_ssl);
            if (ringbuffer_is_empty(&ps->ring_ssl2clear)) {
                if (ps->want_shutdown) {
                    shutdown_proxy(ps, SHUTDOWN_SSL);
                    return; // dealloc'd
                }
                ev_io_stop(loop, &ps->ev_w_clear);
            }
        }
        else {
            ringbuffer_read_skip(&ps->ring_ssl2clear, t);
        }
    }
    else {
        assert(t == -1);
        handle_socket_errno(ps, fd == ps->fd_down ? 1 : 0);
    }
}

/* Continue/complete the asynchronous connect() before starting data transmission
 * between front/backend */
static void handle_connect(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    int t;
    proxystate *ps = (proxystate *)w->data;
    t = connect(ps->fd_down, ps->addr_down->addr->ai_addr, ps->addr_down->addr->ai_addrlen);
    if (!t || errno == EISCONN || !errno) {
        ev_io_stop(loop, &ps->ev_w_connect);
        ev_timer_stop(loop, &ps->ev_t_connect);

        if (!ps->clear_connected) {
            struct sockaddr_storage addr;
            socklen_t sl;

            sl = sizeof(addr);
            getsockname(ps->fd_down, (struct sockaddr*)&addr, &sl);
            ps->connect_port = ntohs(((struct sockaddr_in*)&addr)->sin_port);
            VERBOSEPROXY(ps, "backend connected\n");

            ps->clear_connected = 1;

            /* if incoming buffer is not full */
            if (!ringbuffer_is_full(&ps->ring_clear2ssl))
                safe_enable_io(ps, &ps->ev_r_clear);

            /* if outgoing buffer is not empty */
            if (!ringbuffer_is_empty(&ps->ring_ssl2clear))
                // not safe.. we want to resume stream even during half-closed
                ev_io_start(loop, &ps->ev_w_clear);
        }
        else {
            /* Clear side already connected so connect is on secure side: perform handshake */
            start_handshake(ps, SSL_ERROR_WANT_WRITE);
        }
    }
    else if (errno == EINPROGRESS || errno == EINTR || errno == EALREADY) {
        /* do nothing, we'll get phoned home again... */
    }
    else {
        ERRPROXY(ps, "{backend-connect}: %s\n", strerror(errno));
        shutdown_proxy(ps, SHUTDOWN_CONNECT);
    }
}

static void connect_timeout(EV_P_ ev_timer *w, int revents)
{
    (void) loop;
    (void) revents;
    proxystate *ps = (proxystate *)w->data;
    ERRPROXY(ps,"backend connect timeout\n");
    //shutdown_proxy(ps, SHUTDOWN_HARD);
}

/* Upon receiving a signal from OpenSSL that a handshake is required, re-wire
 * the read/write events to hook up to the handshake handlers */
static void start_handshake(proxystate *ps, int err) {
    ev_io_stop(loop, &ps->ev_r_ssl);
    ev_io_stop(loop, &ps->ev_w_ssl);

    ps->handshaked = 0;

    VERBOSEPROXY(ps,"ssl handshake start\n");
    if (err == SSL_ERROR_WANT_READ)
        ev_io_start(loop, &ps->ev_r_handshake);
    else if (err == SSL_ERROR_WANT_WRITE)
        ev_io_start(loop, &ps->ev_w_handshake);
    ev_timer_start(loop, &ps->ev_t_handshake);
}

/* After OpenSSL is done with a handshake, re-wire standard read/write handlers
 * for data transmission */
static void end_handshake(proxystate *ps) {
    char tcp6_address_string[INET6_ADDRSTRLEN];
    size_t written = 0;
    ev_io_stop(loop, &ps->ev_r_handshake);
    ev_io_stop(loop, &ps->ev_w_handshake);
    ev_timer_stop(loop, &ps->ev_t_handshake);

    {
	X509* cert;
	int cert_ok = 1;

	cert = SSL_get_peer_certificate(ps->ssl);
	if (cert == NULL && CONFIG->REQUIRE_PEER_CERT) {
	    ERRPROXY(ps, "no peer certificate provided\n");
	    cert_ok = 0;
	} else {
	    int result = SSL_get_verify_result(ps->ssl);
	    if (result == X509_V_OK) {
		LOGPROXY(ps, "peer certificate verified\n");
	    } else {
		ERRPROXY(ps, "peer certificate verification failure: %d", result);
		cert_ok = 0;
	    }
	}
	X509_free(cert);
	if (!cert_ok) {
	    shutdown_proxy(ps, SHUTDOWN_SSLERR);
	    return;
	}
    }
    VERBOSEPROXY(ps,"ssl end handshake\n");
    /* Disable renegotiation (CVE-2009-3555) */
    if (ps->ssl->s3) {
        ps->ssl->s3->flags |= SSL3_FLAGS_NO_RENEGOTIATE_CIPHERS;
    }
    ps->handshaked = 1;

    /* Check if clear side is connected */
    if (!ps->clear_connected) {
        if (CONFIG->WRITE_PROXY_LINE) {
            char *ring_pnt = ringbuffer_write_ptr(&ps->ring_ssl2clear);
            assert(ps->remote_ip.ss_family == AF_INET ||
                   ps->remote_ip.ss_family == AF_INET6);
            if(ps->remote_ip.ss_family == AF_INET) {
               struct sockaddr_in* addr = (struct sockaddr_in*)&ps->remote_ip;
               written = snprintf(ring_pnt,
        			  ps->ring_ssl2clear.data_len,
                                  tcp_proxy_line,
                                  "TCP4",
                                  inet_ntoa(addr->sin_addr),
                                  ntohs(addr->sin_port));
               }
               else if (ps->remote_ip.ss_family == AF_INET6) {
                        struct sockaddr_in6* addr = (struct sockaddr_in6*)&ps->remote_ip;
                        inet_ntop(AF_INET6,&(addr->sin6_addr),tcp6_address_string,INET6_ADDRSTRLEN);
                        written = snprintf(ring_pnt,
                        	  ps->ring_ssl2clear.data_len,
                                  tcp_proxy_line,
                                  "TCP6",
                                  tcp6_address_string,
                                  ntohs(addr->sin6_port));
            }   
            ringbuffer_write_append(&ps->ring_ssl2clear, written);
            ps->proxy_clear_len = written;
        }
        else if (CONFIG->WRITE_IP_OCTET) {
            char *ring_pnt = ringbuffer_write_ptr(&ps->ring_ssl2clear);
            assert(ps->remote_ip.ss_family == AF_INET ||
                   ps->remote_ip.ss_family == AF_INET6);
            *ring_pnt++ = (unsigned char) ps->remote_ip.ss_family;
            if (ps->remote_ip.ss_family == AF_INET6) {
                memcpy(ring_pnt, &((struct sockaddr_in6 *) &ps->remote_ip)
                       ->sin6_addr.s6_addr, 16U);
                ringbuffer_write_append(&ps->ring_ssl2clear, 1U + 16U);
                ps->proxy_clear_len = 1 + 16;
            }
            else {
                memcpy(ring_pnt, &((struct sockaddr_in *) &ps->remote_ip)
                       ->sin_addr.s_addr, 4U);
                ringbuffer_write_append(&ps->ring_ssl2clear, 1U + 4U);
                ps->proxy_clear_len = 1 + 4;
            }
        }
	/* start connect now */
        if (!start_connect(ps)) {
            return;
        }
    }
    else {
        /* stud used in client mode, keep client session ) */
        if (!SSL_session_reused(ps->ssl)) {
            if (client_session)
                SSL_SESSION_free(client_session);
            client_session = SSL_get1_session(ps->ssl);
        }
    }

    /* if incoming buffer is not full */
    if (!ringbuffer_is_full(&ps->ring_ssl2clear))
        safe_enable_io(ps, &ps->ev_r_ssl);

    /* if outgoing buffer is not empty */
    if (!ringbuffer_is_empty(&ps->ring_clear2ssl))
        // not safe.. we want to resume stream even during half-closed
        ev_io_start(loop, &ps->ev_w_ssl);
}

static int
log_ssl_error (const proxystate* ps, const char* what)
{
    int e;
    int n = 0;
    while ((e = ERR_get_error())) {
	char buf[1024];
	ERR_error_string_n(e, buf, sizeof(buf));
	ERRPROXY(ps, "SSL error (%s): %s\n", what, buf);
	n++;
    }
    return n;
}

static int
SSLERR (const proxystate* ps, const char* what, int err, int fd)
{
    int client = (fd == ps->fd_up);
    int ret = SHUTDOWN_SSLERR;

    if (client) {
	switch (err) {
	case SSL_ERROR_ZERO_RETURN:
	    VERBOSEPROXY(ps,"Connection cleanly closed (%s) by client\n", what);
	    ret = SHUTDOWN_SSL;
	    break;

	case SSL_ERROR_SYSCALL:
	    if (!log_ssl_error(ps, what)) {
		if (errno == 0) {
		    LOGPROXY(ps,"Connection abruptly closed (%s) by client\n", what);
		    ret = SHUTDOWN_SSL;
		} else if (errno == ECONNRESET || errno == EPIPE) {
		    LOGPROXY(ps,"SSL socket error (%s) on client connection: %s\n", what, strerror(errno));
		    ret = SHUTDOWN_SSL;
		} else {
		    ERRPROXY(ps,"SSL socket error (%s) on client connection: %s\n", what, strerror(errno));
		}
	    }
	    break;

	default:
	    if (!log_ssl_error(ps, what)) {
		ERRPROXY(ps,"SSL error (%s) on client connection: %d\n", what, err);
	    }
	}
    } else {
	switch (err) {
	case SSL_ERROR_ZERO_RETURN:
	    ERRPROXY(ps,"Connection cleanly closed (%s) by backend\n", what);
	    break;

	case SSL_ERROR_SYSCALL:
	    if (!log_ssl_error(ps, what)) {
		ERRPROXY(ps,"SSL socket error (%s) on backend connection: %s\n", what, strerror(errno));
	    }
	    break;

	default:
	    if (!log_ssl_error(ps, what)) {
		ERRPROXY(ps,"SSL error (%s) on backend connection: %d\n", what, err);
	    }
	}
    }
    return ret;
}

/* The libev I/O handler during the OpenSSL handshake phase.  Basically, just
 * let OpenSSL do what it likes with the socket and obey its requests for reads
 * or writes */
static void client_handshake(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    int t;
    proxystate *ps = (proxystate *)w->data;

    VERBOSEPROXY(ps,"ssl client handshake revents=%x\n",revents);
    t = SSL_do_handshake(ps->ssl);
    if (t == 1) {
        end_handshake(ps);
    }
    else {
	int err = SSL_get_error(ps->ssl, t);
        VERBOSEPROXY(ps,"ssl client handshake err=%d\n",err);
        if (err == SSL_ERROR_WANT_READ) {
            ev_io_stop(loop, &ps->ev_w_handshake);
            ev_io_start(loop, &ps->ev_r_handshake);
        }
        else if (err == SSL_ERROR_WANT_WRITE) {
            ev_io_stop(loop, &ps->ev_r_handshake);
            ev_io_start(loop, &ps->ev_w_handshake);
        }
        else {
            shutdown_proxy(ps, SSLERR(ps, "handshake", err, w->fd));
        }
    }
}

static void handshake_timeout(EV_P_ ev_timer *w, int revents)
{
    (void) loop;
    (void) revents;
    proxystate *ps = (proxystate *)w->data;
    VERBOSEPROXY(ps,"SSL handshake timeout\n");
    shutdown_proxy(ps, SHUTDOWN_HANDSHAKE_TIMEOUT);
}


/* and buffer anything we get for writing to the backend */
static void ssl_read(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    int t;    
    proxystate *ps = (proxystate *)w->data;
    if (ps->want_shutdown) {
        ev_io_stop(loop, &ps->ev_r_ssl);
        return;
    }
    if (ringbuffer_is_full(&ps->ring_ssl2clear)) {
	ERRPROXY(ps, "attempt to read ssl when ring full");
	ev_io_stop(loop, &ps->ev_r_ssl);
	return;
    }
    char * buf = ringbuffer_write_ptr(&ps->ring_ssl2clear);
    t = SSL_read(ps->ssl, buf, ps->ring_ssl2clear.data_len);

    /* Fix CVE-2009-3555. Disable reneg if started by client. */
    if (ps->renegotiation) {
	ERRPROXY(ps, "Client renegotiation disabled");
        shutdown_proxy(ps, SHUTDOWN_SSLERR);
        return;
    }

    if (t > 0) {
        if (!ps->buf1_ssl_len) {
	    ps->buf1_ssl_len = (t+1 < (int)sizeof(ps->buf1_ssl)) ? t : (int)sizeof(ps->buf1_ssl)-1;
	    memcpy(ps->buf1_ssl, buf, ps->buf1_ssl_len);
	    ps->buf1_ssl[ps->buf1_ssl_len] = 0;
	}
        ringbuffer_write_append(&ps->ring_ssl2clear, t);
        if (ringbuffer_is_full(&ps->ring_ssl2clear))
            ev_io_stop(loop, &ps->ev_r_ssl);
        if (ps->clear_connected)
            safe_enable_io(ps, &ps->ev_w_clear);
    }
    else {
        int err = SSL_get_error(ps->ssl, t);
        if (err == SSL_ERROR_WANT_WRITE) {
            start_handshake(ps, err);
        }
        else if (err == SSL_ERROR_WANT_READ) { } /* incomplete SSL data */
        else {
            SSLERR(ps, "read", err, w->fd);
            shutdown_proxy(ps, SHUTDOWN_SSLERR);
        }
    }
}

/* Write some previously-buffered backend data upstream on the
 * secure socket using OpenSSL */
static void ssl_write(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    proxystate *ps = (proxystate *)w->data;
    assert(!ringbuffer_is_empty(&ps->ring_clear2ssl));
    do {
        int sz;
	char * next = ringbuffer_read_next(&ps->ring_clear2ssl, &sz);
	int t = SSL_write(ps->ssl, next, sz);
	if (t > 0) {
	    if (t == sz) {
		ringbuffer_read_pop(&ps->ring_clear2ssl);
		if (ps->clear_connected) {
		    safe_enable_io(ps, &ps->ev_r_clear); // can be re-enabled b/c we've popped
		}
	    }
	    else {
		ringbuffer_read_skip(&ps->ring_clear2ssl, t);
		return;
	    }
	}
	else {
	    int err = SSL_get_error(ps->ssl, t);
	    if (err == SSL_ERROR_WANT_READ) {
		start_handshake(ps, err);
	    }
	    else if (err == SSL_ERROR_WANT_WRITE) {} /* incomplete SSL data */
	    else {
		SSLERR(ps, "write", err, w->fd);
		shutdown_proxy(ps, SHUTDOWN_SSLERR);
	    }
	    return;
	}
    } while (!ringbuffer_is_empty(&ps->ring_clear2ssl));
    if (ps->want_shutdown) {
	shutdown_proxy(ps, SHUTDOWN_CLEAR);
    } else {
	ev_io_stop(loop, &ps->ev_w_ssl);
    }
}

/* libev read handler for the bound socket.  Socket is accepted,
 * the proxystate is allocated and initalized, and we're off the races
 * connecting to the backend */
static void handle_accept(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    (void) loop;
    uint64_t now = get_usec();
    struct sockaddr_storage addr;
    socklen_t sl = sizeof(addr);
    int client = accept(w->fd, (struct sockaddr *) &addr, &sl);
    if (client == -1) {
        switch (errno) {
        case EMFILE:
            ERR("{client} accept() failed; too many open files for this process\n");
            break;

        case ENFILE:
            ERR("{client} accept() failed; too many open files for this system\n");
            break;

        default:
            if (errno != EINTR && errno != EWOULDBLOCK && errno != EAGAIN && errno != ENOTTY && errno != ECONNABORTED) {
        	SOCKERR("{client} accept() failed");
            }
        }
        return;
    }

    int flag = 1;
    int ret = setsockopt(client, IPPROTO_TCP, TCP_NODELAY, (char *)&flag, sizeof(flag) );
    if (ret == -1) {
      SOCKERR("Couldn't setsockopt on client (TCP_NODELAY)");
    }
#ifdef TCP_CWND
    int cwnd = 10;
    ret = setsockopt(client, IPPROTO_TCP, TCP_CWND, &cwnd, sizeof(cwnd));
    if (ret == -1) {
      SOCKERR("Couldn't setsockopt on client (TCP_CWND)");
    }
#endif

    setnonblocking(client);
    settcpkeepalive(client);

    struct stud_config_addr* backaddr = get_backaddr();
    int back = create_back_socket(backaddr);

    if (back == -1) {
        close(client);
        ERR("{backend-socket}: %s\n", strerror(errno));
        return;
    }

    SSL_CTX * ctx = (SSL_CTX *)w->data;
    SSL *ssl = SSL_new(ctx);
    long mode = SSL_MODE_ENABLE_PARTIAL_WRITE;
#ifdef SSL_MODE_RELEASE_BUFFERS
    mode |= SSL_MODE_RELEASE_BUFFERS;
#endif
    SSL_set_mode(ssl, mode);
    SSL_set_accept_state(ssl);
    SSL_set_fd(ssl, client);
    SSL_set_tlsext_debug_callback(ssl, tlsext_debug_callback);

    proxystate *ps = (proxystate *)malloc(sizeof(proxystate));

    ps->t_start = now;
    ps->fd_up = client;
    ps->fd_down = back;
    ps->addr_down = backaddr;
    ps->ssl = ssl;
    ps->want_shutdown = 0;
    ps->clear_connected = 0;
    ps->handshaked = 0;
    ps->renegotiation = 0;
    ps->want_sha2 = 0;
    ps->remote_ip = addr;
    ps->connect_port = 0;
    ringbuffer_init(&ps->ring_clear2ssl, CONFIG->RING_SLOTS, CONFIG->RING_DATA_LEN);
    ringbuffer_init(&ps->ring_ssl2clear, CONFIG->RING_SLOTS, CONFIG->RING_DATA_LEN);
    ps->buf1_ssl[0] = 0;
    ps->buf1_ssl_len = 0;
    ps->buf1_clear[0] = 0;
    ps->buf1_clear_len = 0;
    ps->proxy_clear_len = 0;
    ps->ssl_info_where = 0;
    ps->ssl_info_ret = 0;
    ps->ssl_info_state[0] = 0;
    ps->socket_err = 0;

    /* set up events */
    ev_io_init(&ps->ev_r_ssl, ssl_read, client, EV_READ);
    ev_io_init(&ps->ev_w_ssl, ssl_write, client, EV_WRITE);

    ev_io_init(&ps->ev_r_handshake, client_handshake, client, EV_READ);
    ev_io_init(&ps->ev_w_handshake, client_handshake, client, EV_WRITE);
    ev_timer_init(&ps->ev_t_handshake, handshake_timeout, CONFIG->SSL_HANDSHAKE_TIMEOUT, 0.);

    ev_io_init(&ps->ev_w_connect, handle_connect, back, EV_WRITE);
    ev_timer_init(&ps->ev_t_connect, connect_timeout, CONFIG->BACKEND_CONNECT_TIMEOUT, 0.);

    ev_io_init(&ps->ev_w_clear, clear_write, back, EV_WRITE);
    ev_io_init(&ps->ev_r_clear, clear_read, back, EV_READ);

    ps->ev_r_ssl.data = ps;
    ps->ev_w_ssl.data = ps;
    ps->ev_r_clear.data = ps;
    ps->ev_w_clear.data = ps;
    ps->ev_w_connect.data = ps;
    ps->ev_t_connect.data = ps;
    ps->ev_r_handshake.data = ps;
    ps->ev_w_handshake.data = ps;
    ps->ev_t_handshake.data = ps;

    /* Link back proxystate to SSL state */
    SSL_set_app_data(ssl, ps);

    VERBOSEPROXY(ps, "proxy connect\n");

    start_handshake(ps, SSL_ERROR_WANT_READ); /* for client-first handshake */
}


static void check_ppid(struct ev_loop *loop, ev_timer *w, int revents) {
    (void) revents;
    pid_t ppid = getppid();
    if (ppid != master_pid) {
        ERR("{core} Process %d detected parent death, closing listener socket.\n", child_num);
        ev_timer_stop(loop, w);
        ev_io_stop(loop, &listener);
        close(listener_socket);
    }

}

static void handle_clear_accept(struct ev_loop *loop, ev_io *w, int revents) {
    (void) revents;
    (void) loop;
    uint64_t now = get_usec();
    struct sockaddr_storage addr;
    socklen_t sl = sizeof(addr);
    int client = accept(w->fd, (struct sockaddr *) &addr, &sl);
    if (client == -1) {
        switch (errno) {
        case EMFILE:
            ERR("{client} accept() failed; too many open files for this process\n");
            break;

        case ENFILE:
            ERR("{client} accept() failed; too many open files for this system\n");
            break;

        default:
            if (errno != EINTR && errno != EWOULDBLOCK && errno != EAGAIN) {
        	SOCKERR("{client} accept() failed");
        	exit(1);
            }
            break;
        }
        return;
    }

    int flag = 1;
    int ret = setsockopt(client, IPPROTO_TCP, TCP_NODELAY, (char *)&flag, sizeof(flag) );
    if (ret == -1) {
      ERR("Couldn't setsockopt on client (TCP_NODELAY): %s\n", strerror(errno));
    }
#ifdef TCP_CWND
    int cwnd = 10;
    ret = setsockopt(client, IPPROTO_TCP, TCP_CWND, &cwnd, sizeof(cwnd));
    if (ret == -1) {
      ERR("Couldn't setsockopt on client (TCP_CWND): %s\n", strerror(errno));
    }
#endif

    setnonblocking(client);
    settcpkeepalive(client);

    SSL_CTX * ctx = (SSL_CTX *)w->data;
    SSL *ssl = SSL_new(ctx);

    proxystate *ps = (proxystate *)malloc(sizeof(proxystate));
    memset(ps, 0, sizeof(proxystate));

    ps->t_start = now;
    ps->fd_up = client;
    ps->fd_down = -1;
    ps->addr_down = NULL;
    ps->ssl = ssl;
    ps->want_shutdown = 0;
    ps->clear_connected = 1;
    ps->handshaked = 0;
    ps->renegotiation = 0;
    ps->remote_ip = addr;
    ringbuffer_init(&ps->ring_clear2ssl, CONFIG->RING_SLOTS, CONFIG->RING_DATA_LEN);
    ringbuffer_init(&ps->ring_ssl2clear, CONFIG->RING_SLOTS, CONFIG->RING_DATA_LEN);

    /* set up events */
    ev_io_init(&ps->ev_r_clear, clear_read, client, EV_READ);
    ev_io_init(&ps->ev_w_clear, clear_write, client, EV_WRITE);

    ps->ev_r_ssl.data = ps;
    ps->ev_w_ssl.data = ps;
    ps->ev_r_clear.data = ps;
    ps->ev_w_clear.data = ps;
    ps->ev_w_connect.data = ps;
    ps->ev_r_handshake.data = ps;
    ps->ev_w_handshake.data = ps;
    ps->ev_t_handshake.data = ps;

    ev_io_start(loop, &ps->ev_r_clear);
    if (!CONFIG->BACKEND_CONNECT) {
        ssl_client_setup(ps, get_backaddr());
    }
}

/* Set up the child (worker) process including libev event loop, read event
 * on the bound socket, etc */
static void handle_connections() {
    LOG("{core} Process %d online\n", child_num);

    /* child cannot create new children... */
    create_workers = 0;

#if defined(CPU_ZERO) && defined(CPU_SET)
    cpu_set_t cpus;

    CPU_ZERO(&cpus);
    CPU_SET(child_num, &cpus);

    int res = sched_setaffinity(0, sizeof(cpus), &cpus);
    if (!res)
        LOG("{core} Successfully attached to CPU #%d\n", child_num);
    else
        ERR("{core-warning} Unable to attach to CPU #%d; do you have that many cores?\n", child_num);
#endif

    loop = ev_default_loop(EVFLAG_AUTO);

    ev_timer timer_ppid_check;
    ev_timer_init(&timer_ppid_check, check_ppid, 1.0, 1.0);
    ev_timer_start(loop, &timer_ppid_check);

    ev_io_init(&listener, (CONFIG->PMODE == SSL_CLIENT) ? handle_clear_accept : handle_accept, listener_socket, EV_READ);
    listener.data = ssl_ctx;
    ev_io_start(loop, &listener);

    ev_loop(loop, 0);
    ERR("{core} Child %d exiting.\n", child_num);
    exit(1);
}

void change_root() {
    if (chroot(CONFIG->CHROOT) == -1)
        fail("chroot");
    if (chdir("/"))
        fail("chdir");
}

void drop_privileges() {
    if (CONFIG->GID >= 0 && setgid(CONFIG->GID) < 0)
        fail("setgid failed");
    if (CONFIG->UID >= 0 && setuid(CONFIG->UID) < 0)
        fail("setuid failed");
}


void init_globals() {
#ifdef USE_SHARED_CACHE
    if (CONFIG->SHARED_CACHE) {
        /* cache update peers addresses */
        shcupd_peer_opt *spo = CONFIG->SHCUPD_PEERS;
        struct addrinfo **pai = shcupd_peers;

        while (spo->ip) {
            memset(&hints, 0, sizeof hints);
            hints.ai_family = AF_UNSPEC;
            hints.ai_socktype = SOCK_DGRAM;
            hints.ai_flags = 0;
            const int gai_err = getaddrinfo(spo->ip,
                                spo->port ? spo->port : CONFIG->SHCUPD_PORT, &hints, pai);
            if (gai_err != 0) {
                ERR("{getaddrinfo}: [%s]", gai_strerror(gai_err));
                exit(1);
            }
            spo++;
            pai++;
        }
    }
#endif
    /* child_pids */
    if ((child_pids = calloc(CONFIG->NCORES, sizeof(pid_t))) == NULL)
        fail("calloc");

    if (CONFIG->SYSLOG)
        openlog("stud", LOG_CONS | LOG_PID | LOG_NDELAY, CONFIG->SYSLOG_FACILITY);
}

/* Forks COUNT children starting with START_INDEX.
 * Each child's index is stored in child_num and its pid is stored in child_pids[child_num]
 * so the parent can manage it later. */
void start_children(int start_index, int count) {
    /* don't do anything if we're not allowed to create new children */
    if (!create_workers) return;

    for (child_num = start_index; child_num < start_index + count; child_num++) {
        int pid = fork();
        if (pid == -1) {
            ERR("{core} fork() failed: %s; Goodbye cruel world!\n", strerror(errno));
            exit(1);
        }
        else if (pid == 0) { /* child */
            handle_connections();
            exit(0);
        }
        else { /* parent. Track new child. */
            child_pids[child_num] = pid;
        }
    }
}

/* Forks a new child to replace the old, dead, one with the given PID.*/
void replace_child_with_pid(pid_t pid) {
    int i;

    /* find old child's slot and put a new child there */ 
    for (i = 0; i < CONFIG->NCORES; i++) {
        if (child_pids[i] == pid) {
            start_children(i, 1);
            return;
        }
    }

    ERR("Cannot find index for child pid %d", pid);
}

/* Manage status changes in child processes */
static void do_wait(int __attribute__ ((unused)) signo) {

    int status;
    int pid = wait(&status);

    if (pid == -1) {
        if (errno == ECHILD) {
            ERR("{core} All children have exited! Restarting...\n");
            start_children(0, CONFIG->NCORES);
        }
        else if (errno == EINTR) {
            ERR("{core} Interrupted wait\n");
        }
        else {
            fail("wait");
        }
    }
    else {
        if (WIFEXITED(status)) {
            ERR("{core} Child %d exited with status %d. Replacing...\n", pid, WEXITSTATUS(status));
            replace_child_with_pid(pid);
        }
        else if (WIFSIGNALED(status)) {
            ERR("{core} Child %d was terminated by signal %d. Replacing...\n", pid, WTERMSIG(status));
            replace_child_with_pid(pid);
        }
    }
}

static void sigh_terminate (int __attribute__ ((unused)) signo) {
    /* don't create any more children */
    create_workers = 0;

    /* are we the master? */
    if (getpid() == master_pid) {
        LOG("{core} Received signal %d, shutting down.\n", signo);

        /* kill all children */
        int i;
        for (i = 0; i < CONFIG->NCORES; i++) {
            /* LOG("Stopping worker pid %d.\n", child_pids[i]); */
            if (child_pids[i] > 1 && kill(child_pids[i], SIGTERM) != 0) {
                ERR("{core} Unable to send SIGTERM to worker pid %d: %s\n", child_pids[i], strerror(errno));
            }
        }
        /* LOG("Shutdown complete.\n"); */
    }

    /* this is it, we're done... */
    exit(0);
}

void init_signals() {
    struct sigaction act;

    sigemptyset(&act.sa_mask);
    act.sa_flags = 0;
    act.sa_handler = SIG_IGN;

    /* Avoid getting PIPE signal when writing to a closed file descriptor */
    if (sigaction(SIGPIPE, &act, NULL) < 0)
        fail("sigaction - sigpipe");

    /* We don't care if someone stops and starts a child process with kill (1) */
    act.sa_flags = SA_NOCLDSTOP;

    act.sa_handler = do_wait;

    /* We do care when child processes change status */
    if (sigaction(SIGCHLD, &act, NULL) < 0)
        fail("sigaction - sigchld");

    /* catch INT and TERM signals */
    act.sa_flags = 0;
    act.sa_handler = sigh_terminate;
    if (sigaction(SIGINT, &act, NULL) < 0) {
        ERR("Unable to register SIGINT signal handler: %s\n", strerror(errno));
        exit(1);
    }
    if (sigaction(SIGTERM, &act, NULL) < 0) {
        ERR("Unable to register SIGTERM signal handler: %s\n", strerror(errno));
        exit(1);
    }
}

void daemonize () {
    if (logf == stdout || logf == stderr) {
	logf = NULL;
    }

    /* go to root directory */
    if (chdir("/") != 0) {
        ERR("Unable change directory to /: %s\n", strerror(errno));
        exit(1);
    }

    /* let's make some children, baby :) */
    pid_t pid = fork();
    if (pid < 0) {
        ERR("Unable to daemonize: fork failed: %s\n", strerror(errno));
        exit(1);
    }

    /* am i the parent? */
    if (pid != 0) {
        printf("{core} Daemonized as pid %d.\n", pid);
        exit(0);
    }

    /* close standard streams */
    fclose(stdin);
    fclose(stdout);
    fclose(stderr);

    /* reopen standard streams to null device */
    stdin = fopen(NULL_DEV, "r");
    if (stdin == NULL) {
        ERR("Unable to reopen stdin to %s: %s\n", NULL_DEV, strerror(errno));
        exit(1);
    }
    stdout = fopen(NULL_DEV, "w");
    if (stdout == NULL) {
        ERR("Unable to reopen stdout to %s: %s\n", NULL_DEV, strerror(errno));
        exit(1);
    }
    stderr = fopen(NULL_DEV, "w");
    if (stderr == NULL) {
        ERR("Unable to reopen stderr to %s: %s\n", NULL_DEV, strerror(errno));
        exit(1);
    }

    /* this is child, the new master */
    pid_t s = setsid();
    if (s < 0) {
        ERR("Unable to create new session, setsid(2) failed: %s :: %d\n", strerror(errno), s);
        exit(1);
    }

    LOG("Successfully daemonized as pid %d.\n", getpid());
}

void openssl_check_version() {
    /* detect OpenSSL version in runtime */
    openssl_version = SSLeay();

    /* check if we're running the same openssl that we were */
    /* compiled with */
    if ((openssl_version ^ OPENSSL_VERSION_NUMBER) & ~0xff0L) {
        ERR(
	    "WARNING: {core} OpenSSL version mismatch; stud was compiled with %lx, now using %lx.\n",
	    (unsigned long int) OPENSSL_VERSION_NUMBER,
	    (unsigned long int) openssl_version
	);
	/* now what? exit now? */
	/* exit(1); */
    }

    LOG("{core} Using OpenSSL version %lx.\n", (unsigned long int) openssl_version);
}

/* Process command line args, create the bound socket,
 * spawn child (worker) processes, and respawn if any die */
int main(int argc, char **argv) {
    // initialize configuration
    CONFIG = config_new();

    // parse command line
    config_parse_cli(argc, argv, CONFIG);

    if (CONFIG->LOG_FILENAME) {
	FILE* f;
	if ((f = fopen(CONFIG->LOG_FILENAME, "a")) == NULL) {
	    ERR("FATAL: Unable to open log file: %s: %s\n", CONFIG->LOG_FILENAME, strerror(errno));
	    exit(2);
	}
	logf = f;
	if (CONFIG->UID >=0 || CONFIG->GID >= 0) {
	    fchown(fileno(logf), CONFIG->UID, CONFIG->GID);
	}
	fstat(fileno(logf), &logf_st);
	logf_check_t = time(NULL);
    } else {
	logf = CONFIG->QUIET ? stderr : stdout;
    }
    setbuf(logf, NULL);

    create_workers = 1;

    openssl_check_version();

    init_signals();

    init_globals();

    listener_socket = create_main_socket();

#ifdef USE_SHARED_CACHE
    if (CONFIG->SHCUPD_PORT) {
        /* create socket to send(children) and
               receive(parent) cache updates */
    	shcupd_socket = create_shcupd_socket();
    }
#endif /* USE_SHARED_CACHE */

    /* load certificate, pass to handle_connections */
    ssl_ctx = init_openssl(0);
    if (CONFIG->CERT_FILE_SHA2) {
        ssl_ctx_sha2 = init_openssl(1);
    } else {
        ssl_ctx_sha2 = ssl_ctx;
    }

    if (CONFIG->CHROOT && CONFIG->CHROOT[0])
        change_root();

    if (CONFIG->UID >= 0 || CONFIG->GID >= 0)
        drop_privileges();

    /* should we daemonize ?*/
    if (CONFIG->DAEMONIZE) {
        /* become a daemon */
        daemonize();
    }

    master_pid = getpid();

    start_children(0, CONFIG->NCORES);

#ifdef USE_SHARED_CACHE
    if (CONFIG->SHCUPD_PORT) {
        /* start event loop to receive cache updates */

        loop = ev_default_loop(EVFLAG_AUTO);

        ev_io_init(&shcupd_listener, handle_shcupd, shcupd_socket, EV_READ);
        ev_io_start(loop, &shcupd_listener);
            
        ev_loop(loop, 0);
    }
#endif /* USE_SHARED_CACHE */

    for (;;) {
        /* Sleep and let the children work.
         * Parent will be woken up if a signal arrives */
        pause();
    }
    
    exit(0); /* just a formality; we never get here */
}
