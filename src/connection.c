/* Icecast
 *
 * This program is distributed under the GNU General Public License, version 2.
 * A copy of this license is included with this source.
 *
 * Copyright 2000-2004, Jack Moffitt <jack@xiph.org,
 *                      Michael Smith <msmith@xiph.org>,
 *                      oddsock <oddsock@xiph.org>,
 *                      Karl Heyes <karl@xiph.org>
 *                      and others (see AUTHORS for details).
 */

/* -*- c-basic-offset: 4; indent-tabs-mode: nil; -*- */
#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#ifdef HAVE_POLL
#include <sys/poll.h>
#endif
#include <sys/types.h>
#include <sys/stat.h>

#ifndef _WIN32
#include <sys/socket.h>
#include <netinet/in.h>
#else
#include <winsock2.h>
#define snprintf _snprintf
#define strcasecmp stricmp
#define strncasecmp strnicmp
#endif

#include "compat.h"

#include "thread/thread.h"
#include "avl/avl.h"
#include "net/sock.h"
#include "httpp/httpp.h"

#include "cfgfile.h"
#include "global.h"
#include "util.h"
#include "connection.h"
#include "refbuf.h"
#include "client.h"
#include "stats.h"
#include "logging.h"
#include "xslt.h"
#include "fserve.h"
#include "sighandler.h"

#include "yp.h"
#include "source.h"
#include "format.h"
#include "format_mp3.h"
#include "event.h"
#include "admin.h"
#include "auth.h"

#define CATMODULE "connection"

/* Two different major types of source authentication.
   Shoutcast style is used only by the Shoutcast DSP
   and is a crazy version of HTTP.  It looks like :
     Source Client -> Connects to port + 1
     Source Client -> sends encoder password (plaintext)\r\n
     Icecast -> reads encoder password, if ok, sends OK2\r\n, else disconnects
     Source Client -> reads OK2\r\n, then sends http-type request headers
                      that contain the stream details (icy-name, etc..)
     Icecast -> reads headers, stores them
     Source Client -> starts sending MP3 data
     Source Client -> periodically updates metadata via admin.cgi call

   Icecast auth style uses HTTP and Basic Authorization.
*/
#define NOAUTH_SOURCE_AUTH 2
#define SHOUTCAST_SOURCE_AUTH 1
#define ICECAST_SOURCE_AUTH 0

typedef struct connection_queue_tag {
    connection_t *con;
    refbuf_t *refbuf;
    http_parser_t *parser;
    client_t *client;
    struct connection_queue_tag *next;
} connection_queue_t;

typedef struct
{
    char *filename;
    time_t file_recheck;
    time_t file_mtime;
    avl_tree *contents;
} cache_file_contents;

static spin_t _connection_lock;
static volatile unsigned long _current_id = 0;
static int _initialized = 0;
static volatile int _connection_running = 0;
static volatile connection_queue_t *_con_queue = NULL, **_con_queue_tail = &_con_queue;
static cond_t *_connection_cond;
static thread_type *_connection_thread_id;

static int ssl_ok;
#ifdef HAVE_OPENSSL
static SSL_CTX *ssl_ctx;
#endif

/* filtering client connection based on IP */
cache_file_contents banned_ip, allowed_ip;

rwlock_t _source_shutdown_rwlock;

static int _handle_client (client_t *client);
static int _handle_shoutcast_stage1 (connection_queue_t *node, char *shoutcast_mount, mount_proxy *mountinfo);
static int _connection_process (connection_queue_t *node);
static void *_connection_thread (void *arg);

static int compare_ip (void *arg, void *a, void *b)
{
    const char *ip = (const char *)a;
    const char *pattern = (const char *)b;

    return strcmp (pattern, ip);
}


static int free_filtered_ip (void*x)
{
    free (x);
    return 1;
}


void connection_initialize(void)
{
    if (_initialized) return;

    thread_spin_create (&_connection_lock);
    thread_mutex_create(&move_clients_mutex);
    thread_rwlock_create(&_source_shutdown_rwlock);
    thread_cond_init(&global.shutdown_cond);
    _con_queue = NULL;
    _con_queue_tail = &_con_queue;

    banned_ip.contents = NULL;
    banned_ip.file_mtime = 0;

    allowed_ip.contents = NULL;
    allowed_ip.file_mtime = 0;

    _connection_running = 1;
    /* (XXX)xaiki: need a way to make it go away on shutdown, ok for now */
    _connection_thread_id = thread_create ("Connection Thread", _connection_thread,
					   NULL, THREAD_DETACHED);
    _connection_cond = thread_cond_create ();

    _initialized = 1;
}

void connection_shutdown(void)
{
    if (!_initialized) return;

    _connection_running = 0;
    thread_cond_signal(_connection_cond);
    DEBUG0 ("waiting for connection thread");
    thread_join(_connection_thread_id);

#ifdef HAVE_OPENSSL
    SSL_CTX_free (ssl_ctx);
#endif
    if (banned_ip.contents)  avl_tree_free (banned_ip.contents, free_filtered_ip);
    if (allowed_ip.contents) avl_tree_free (allowed_ip.contents, free_filtered_ip);

    thread_cond_destroy (_connection_cond);
    free (_connection_cond);

    thread_cond_destroy(&global.shutdown_cond);
    thread_rwlock_destroy(&_source_shutdown_rwlock);
    thread_spin_destroy (&_connection_lock);
    thread_mutex_destroy(&move_clients_mutex);

    _initialized = 0;
}

static unsigned long _next_connection_id(void)
{
    unsigned long id;

    thread_spin_lock (&_connection_lock);
    id = _current_id++;
    thread_spin_unlock (&_connection_lock);

    return id;
}


#ifdef HAVE_OPENSSL
static void get_ssl_certificate (ice_config_t *config)
{
    SSL_METHOD *method;
    ssl_ok = 0;

    SSL_load_error_strings();                /* readable error messages */
    SSL_library_init();                      /* initialize library */

    method = SSLv23_server_method();
    ssl_ctx = SSL_CTX_new (method);

    do
    {
        if (config->cert_file == NULL)
            break;
        if (SSL_CTX_use_certificate_file (ssl_ctx, config->cert_file, SSL_FILETYPE_PEM) <= 0)
        {
            WARN1 ("Invalid cert file %s", config->cert_file);
            break;
        }
        if (SSL_CTX_use_PrivateKey_file (ssl_ctx, config->cert_file, SSL_FILETYPE_PEM) <= 0)
        {
            WARN1 ("Invalid private key file %s", config->cert_file);
            break;
        }
        if (!SSL_CTX_check_private_key (ssl_ctx))
        {
            ERROR1 ("Invalid %s - Private key does not match cert public key", config->cert_file);
            break;
        }
        ssl_ok = 1;
        INFO1 ("SSL certificate found at %s", config->cert_file);
        return;
    } while (0);
    INFO0 ("No SSL capability on any configured ports");
}


/* handlers for reading and writing a connection_t when there is ssl
 * configured on the listening port
 */
static int connection_read_ssl (connection_t *con, void *buf, size_t len)
{
    int bytes = SSL_read (con->ssl, buf, len);

    if (bytes < 0)
    {
        switch (SSL_get_error (con->ssl, bytes))
        {
            case SSL_ERROR_WANT_READ:
            case SSL_ERROR_WANT_WRITE:
                return -1;
        }
        con->error = 1;
    }
    return bytes;
}

static int connection_send_ssl (connection_t *con, const void *buf, size_t len)
{
    int bytes = SSL_write (con->ssl, buf, len);

    if (bytes < 0)
    {
        switch (SSL_get_error (con->ssl, bytes))
        {
            case SSL_ERROR_WANT_READ:
            case SSL_ERROR_WANT_WRITE:
                return -1;
        }
        con->error = 1;
    }
    else
        con->sent_bytes += bytes;
    return bytes;
}
#else

/* SSL not compiled in, so at least log it */
static void get_ssl_certificate (ice_config_t *config)
{
    ssl_ok = 0;
    INFO0 ("No SSL capability");
}
#endif /* HAVE_OPENSSL */


/* handlers (default) for reading and writing a connection_t, no encrpytion
 * used just straight access to the socket
 */
static int connection_read (connection_t *con, void *buf, size_t len)
{
    int bytes = sock_read_bytes (con->sock, buf, len);
    if (bytes == 0)
        con->error = 1;
    if (bytes == -1 && !sock_recoverable (sock_error()))
        con->error = 1;
    return bytes;
}

static int connection_send (connection_t *con, const void *buf, size_t len)
{
    int bytes = sock_write_bytes (con->sock, buf, len);
    if (bytes < 0)
    {
        if (!sock_recoverable (sock_error()))
            con->error = 1;
    }
    else
        con->sent_bytes += bytes;
    return bytes;
}


/* function to handle the re-populating of the avl tree containing IP addresses
 * for deciding whether a connection of an incoming request is to be dropped.
 */
static void recheck_ip_file (cache_file_contents *cache)
{
    time_t now = time(NULL);
    if (now >= cache->file_recheck)
    {
        struct stat file_stat;
        FILE *file = NULL;
        int count = 0;
        avl_tree *new_ips;
        char line [MAX_LINE_LEN];

        cache->file_recheck = now + 10;
        if (cache->filename == NULL)
        {
            if (cache->contents)
            {
                avl_tree_free (cache->contents, free_filtered_ip);
                cache->contents = NULL;
            }
            return;
        }
        if (stat (cache->filename, &file_stat) < 0)
        {
            WARN2 ("failed to check status of \"%s\": %s", cache->filename, strerror(errno));
            return;
        }
        if (file_stat.st_mtime == cache->file_mtime)
            return; /* common case, no update to file */

        cache->file_mtime = file_stat.st_mtime;

        file = fopen (cache->filename, "r");
        if (file == NULL)
        {
            WARN2("Failed to open file \"%s\": %s", cache->filename, strerror (errno));
            return;
        }

        new_ips = avl_tree_new (compare_ip, NULL);

        while (get_line (file, line, MAX_LINE_LEN))
        {
            char *str;
            if(!line[0] || line[0] == '#')
                continue;
            count++;
            str = strdup (line);
            if (str)
                avl_insert (new_ips, str);
        }
        fclose (file);
        INFO2 ("%d entries read from file \"%s\"", count, cache->filename);

        if (cache->contents) avl_tree_free (cache->contents, free_filtered_ip);
        cache->contents = new_ips;
    }
}


/* return 0 if the passed ip address is not to be handled by icecast, non-zero otherwise */
static int accept_ip_address (char *ip)
{
    void *result;

    recheck_ip_file (&banned_ip);
    recheck_ip_file (&allowed_ip);

    if (banned_ip.contents)
    {
        if (avl_get_by_key (banned_ip.contents, ip, &result) == 0)
        {
            DEBUG1 ("%s is banned", ip);
            return 0;
        }
    }
    if (allowed_ip.contents)
    {
        if (avl_get_by_key (allowed_ip.contents, ip, &result) == 0)
        {
            DEBUG1 ("%s is allowed", ip);
            return 1;
        }
        else
        {
            DEBUG1 ("%s is not allowed", ip);
            return 0;
        }
    }
    return 1;
}


connection_t *connection_create (sock_t sock, sock_t serversock, char *ip)
{
    connection_t *con;
    con = (connection_t *)calloc(1, sizeof(connection_t));
    if (con)
    {
        con->sock = sock;
        con->serversock = serversock;
        con->con_time = time(NULL);
        con->id = _next_connection_id();
        con->ip = ip;
        con->read = connection_read;
        con->send = connection_send;
    }

    return con;
}

/* prepare connection for interacting over a SSL connection
 */
void connection_uses_ssl (connection_t *con)
{
#ifdef HAVE_OPENSSL
    con->read = connection_read_ssl;
    con->send = connection_send_ssl;
    con->ssl = SSL_new (ssl_ctx);
    SSL_set_accept_state (con->ssl);
    SSL_set_fd (con->ssl, con->sock);
#endif
}

static sock_t wait_for_serversock(int timeout)
{
#ifdef HAVE_POLL
    struct pollfd ufds [global.server_sockets];
    int i, ret;

    for(i=0; i < global.server_sockets; i++) {
        ufds[i].fd = global.serversock[i];
        ufds[i].events = POLLIN;
        ufds[i].revents = 0;
    }

    ret = poll(ufds, global.server_sockets, timeout);
    if(ret < 0) {
        return SOCK_ERROR;
    }
    else if(ret == 0) {
        return SOCK_ERROR;
    }
    else {
        int dst;
        for(i=0; i < global.server_sockets; i++) {
            if(ufds[i].revents & POLLIN)
                return ufds[i].fd;
            if(ufds[i].revents & (POLLHUP|POLLERR|POLLNVAL))
            {
                if (ufds[i].revents & (POLLHUP|POLLERR))
                {
                    sock_close (global.serversock[i]);
                    WARN0("Had to close a listening socket");
                }
                global.serversock[i] = SOCK_ERROR;
            }
        }
        /* remove any closed sockets */
        for(i=0, dst=0; i < global.server_sockets; i++)
        {
            if (global.serversock[i] == SOCK_ERROR)
                continue;
            if (i!=dst)
                global.serversock[dst] = global.serversock[i];
            dst++;
        }
        global.server_sockets = dst;
        return SOCK_ERROR;
    }
#else
    fd_set rfds;
    struct timeval tv, *p=NULL;
    int i, ret;
    sock_t max = SOCK_ERROR;

    FD_ZERO(&rfds);

    for(i=0; i < global.server_sockets; i++) {
        FD_SET(global.serversock[i], &rfds);
        if (max == SOCK_ERROR || global.serversock[i] > max)
            max = global.serversock[i];
    }

    if(timeout >= 0) {
        tv.tv_sec = timeout/1000;
        tv.tv_usec = (timeout % 1000) * 1000;
        p = &tv;
    }

    ret = select(max+1, &rfds, NULL, NULL, p);
    if(ret < 0) {
        return SOCK_ERROR;
    }
    else if(ret == 0) {
        return SOCK_ERROR;
    }
    else {
        for(i=0; i < global.server_sockets; i++) {
            if(FD_ISSET(global.serversock[i], &rfds))
                return global.serversock[i];
        }
        return SOCK_ERROR; /* Should be impossible, stop compiler warnings */
    }
#endif
}

static connection_t *_accept_connection(int duration)
{
    sock_t sock, serversock;
    char *ip;

    serversock = wait_for_serversock (duration);
    if (serversock == SOCK_ERROR)
        return NULL;

    /* malloc enough room for a full IP address (including ipv6) */
    ip = (char *)malloc(MAX_ADDR_LEN);

    sock = sock_accept(serversock, ip, MAX_ADDR_LEN);
    if (sock != SOCK_ERROR)
    {
        connection_t *con = NULL;
        /* Make any IPv4 mapped IPv6 address look like a normal IPv4 address */
        if (strncmp (ip, "::ffff:", 7) == 0)
            memmove (ip, ip+7, strlen (ip+7)+1);

        if (accept_ip_address (ip)) {
            con = connection_create (sock, serversock, ip);
            if (con)
                return con;
        }
        sock_close (sock);
    }
    else
    {
        if (!sock_recoverable(sock_error()))
        {
            WARN2("accept() failed with error %d: %s", sock_error(), strerror(sock_error()));
            thread_sleep (500000);
        }
    }
    free(ip);
    return NULL;
}

connection_queue_t *_connection_new (connection_t *con)
{
    connection_queue_t *node;
    if (!con)
        return NULL;

    node = calloc (1, sizeof (connection_queue_t));
    if (!node)
        return NULL;

    node->con = con;

    return node;
}

/* add a connection to connection queue. At this point the connection
 * has just been accepted, we push it to the queue and return so that
 * we can keep getting connections in.
 */
static void _add_connection (connection_queue_t *node)
{
    WARN ("added connection");
    *_con_queue_tail = node;
    _con_queue_tail = (volatile connection_queue_t **)&node->next;

    thread_cond_signal(_connection_cond);
}

/* this returns queued clients for the connection thread. headers are
 * already provided, but need to be parsed.
 */
static connection_queue_t *_get_connection(void)
{
    connection_queue_t *node = NULL;

    /* common case, no new connections so don't bother taking locks */
    if (_con_queue) {
        node = (connection_queue_t *)_con_queue;
        _con_queue = node->next;
        if (_con_queue == NULL)
            _con_queue_tail = &_con_queue;
        node->next = NULL;
    } else {
        INFO("sleeping");
        thread_cond_wait(_connection_cond);
        INFO("awake");
    }
    return node;
}

static void destroy_node (connection_queue_t *node) {
    INFO("destroying node");

    if (node->client)
        client_destroy(node->client);
    if (node->parser)
        httpp_destroy(node->parser);
    if (node->refbuf)
        refbuf_release(node->refbuf);
    if (node->con)
        connection_close(node->con);
    free(node);
}

static void *_connection_thread (void *arg)
{
    connection_queue_t *node;
    int err;

    WARN("Launched connection thread");
    while (_connection_running)
    {
        /* XXX(xaiki): this needs to wait on a fd, so we don't kill polar bears */
        node = _get_connection();
        INFO("got node");
        if (!node) {
            continue;
        }
        err = _connection_process (node);
        if (err == -EAGAIN) { /* EAGAIN, put it again at the end of the queue */
            _add_connection (node);
        } else { /* OK or Recoverable ERR */
            if (err < 0) {
                ERROR ("droping node, error = %d", err);
                destroy_node (node);
                continue;
            }
            free(node);
        }
    }

    while (_con_queue) {
        node = _get_connection();
        destroy_node (node);
    }

    INFO0 ("Connection thread shutdown complete");
    return NULL;
}

static int connection_client_setup (connection_queue_t *node) {
    int err;

    global_lock();
    err = client_create (&node->client, node->con, node->parser);
    if (err < 0) {
        client_send_403 (node->client, "Icecast connection limit reached");
        /* don't be too eager as this is an imposed hard limit */
        goto out_fail;
    }

    err = -EINVAL;
    if (sock_set_blocking (node->con->sock, 0) || sock_set_nodelay (node->con->sock)) {
        WARN0 ("failed to set tcp options on client connection, dropping");
        goto out_destroy_client;
    }

/* XXX(xaiki): this should be 1, but actually, it's buggy, the client is already up and all.. */
    err = -ENOENT;
    if (node->con->con_timeout <= time(NULL)) {
        WARN("there might be a bug if you see this");
        goto out_destroy_client;
    }

    global_unlock();

    return 0;

out_destroy_client:
    client_destroy (node->client);
out_fail:
    global_unlock();
    return err;
}

/* we don't need to clean up on err, as we'll go through the node struct and clean all we have inside */
static int _connection_process (connection_queue_t *node) {
    refbuf_t *header;
    http_parser_t *parser = NULL;
    int hdrsize = 0;
    int shoutcast = 0;
    int err;
    char *shoutcast_mount = NULL;
    mount_proxy *mountinfo;

    ice_config_t *config;
    listener_t *listener;

    if (!node->refbuf)
	    node->refbuf = refbuf_new (PER_CLIENT_REFBUF_SIZE);
    header = node->refbuf;

    { /* this code tests for shoutcastness */
        config = config_get_config();
        listener = config_get_listen_sock (config, node->con);

        if (listener) {
            WARN("listner");
            if (listener->shoutcast_compat)
                shoutcast = 1;
            if (listener->ssl && ssl_ok)
                connection_uses_ssl (node->con);
            if (listener->shoutcast_mount) {
                shoutcast_mount = strdup (listener->shoutcast_mount);
            } else {
                shoutcast_mount = config->shoutcast_mount;
            }
        }

        WARN("shoutcast %d, mount %s", shoutcast, shoutcast_mount);

        mountinfo = config_find_mount (config, shoutcast_mount);
        config_release_config();
    }

    if (shoutcast && !header->sync_point) { /* stage2 is actually handled by generic code */
        err = _handle_shoutcast_stage1 (node, shoutcast_mount, mountinfo);
        if (err < 0)
            return err;
    }

    hdrsize = util_read_header (node->con, header, HEADER_READ_ENTIRE);
    if (hdrsize < 0)
    {
        ERROR ("Header read failed");
        return hdrsize;
    }

    /* process normal HTTP headers */
    if (node->parser) {
        parser = node->parser;
    } else {
        parser = node->parser = httpp_create_parser();
        httpp_initialize(parser, NULL);
    }

    err = httpp_parse (parser, header->data, hdrsize);
    if (err == 0) {
        ERROR0("HTTP request parsing failed");
        return -EINVAL;
    }

    if (httpp_getvar (parser, HTTPP_VAR_ERROR_MESSAGE)) {
        ERROR("Error(%s)", httpp_getvar(parser, HTTPP_VAR_ERROR_MESSAGE));
        return err;
    }

    if (header->sync_point && (parser->req_type == httpp_req_source ||
                               parser->req_type == httpp_req_post)) {
	    hdrsize = util_read_header (node->con, header, HEADER_READ_ENTIRE);
	    if (hdrsize < 0) {
            INFO ("Header read failed");
            return hdrsize;
        }
    }

    if (! node->client) {
        err = connection_client_setup (node);
        if (err < 0)
            return err;

        header->len -= hdrsize;
        if (header->len) {
            memmove(header->data, header->data + hdrsize, header->len);
            client_set_queue (node->client, header);
        }
        refbuf_release(header);
    }

    stats_event_inc (NULL, "connections");

    WARN("shoutcast = %d", shoutcast);

    return _handle_client (node->client);
}

void connection_accept_loop (void)
{
    connection_queue_t *node;
    connection_t *con;
    ice_config_t *config;
    int duration = 300;
    int timeout = 0;

    config = config_get_config ();
    get_ssl_certificate (config);
    timeout = config->header_timeout;
    config_release_config ();

    while (global.running == ICE_RUNNING)
    {
        con = _accept_connection (duration);

        if (!con) {
            duration = 300; /* use longer timeouts when nothing waiting */
            continue;
        }

        con->con_timeout = time(NULL) + timeout;

        /* add connection async to the connection queue, then the
         * connection loop will do all the dirty work */
        node =_connection_new (con);
        _add_connection (node);
    }

    /* Give all the other threads notification to shut down */
    thread_cond_broadcast(&global.shutdown_cond);

    /* wait for all the sources to shutdown */
    thread_rwlock_wlock(&_source_shutdown_rwlock);
    thread_rwlock_unlock(&_source_shutdown_rwlock);
}


/* Called when activating a source. Verifies that the source count is not
 * exceeded and applies any initial parameters.
 */
int connection_complete_source (source_t *source, int response)
{
    ice_config_t *config;

    global_lock ();
    DEBUG1 ("sources count is %d", global.sources);

    config = config_get_config();
    if (global.sources < config->source_limit)
    {
        const char *contenttype;
        mount_proxy *mountinfo;
        format_type_t format_type;

        /* setup format handler */
        contenttype = httpp_getvar (source->parser, "content-type");
        if (contenttype != NULL)
        {
            format_type = format_get_type (contenttype);

            if (format_type == FORMAT_ERROR)
            {
                config_release_config();
                global_unlock();
                if (response)
                {
                    client_send_403 (source->client, "Content-type not supported");
                    source->client = NULL;
                }
                WARN1("Content-type \"%s\" not supported, dropping source", contenttype);
                return -1;
            }
        }
        else
        {
            WARN0("No content-type header, falling back to backwards compatibility mode "
                    "for icecast 1.x relays. Assuming content is mp3.");
            format_type = FORMAT_TYPE_GENERIC;
        }

        if (format_get_plugin (format_type, source) < 0)
        {
            global_unlock();
            config_release_config();
            if (response)
            {
                client_send_403 (source->client, "internal format allocation problem");
                source->client = NULL;
            }
            WARN1 ("plugin format failed for \"%s\"", source->mount);
            return -1;
        }

        global.sources++;
        stats_event_args (NULL, "sources", "%d", global.sources);
        global_unlock();

        source->running = 1;
        mountinfo = config_find_mount (config, source->mount);
        source_update_settings (config, source, mountinfo);
        config_release_config();
        slave_rebuild_mounts();

        source->shutdown_rwlock = &_source_shutdown_rwlock;
        DEBUG0 ("source is ready to start");

        return 0;
    }
    WARN1("Request to add source when maximum source limit "
            "reached %d", global.sources);

    global_unlock();
    config_release_config();

    if (response)
    {
        client_send_403 (source->client, "too many sources connected");
        source->client = NULL;
    }

    return -1;
}


static int _check_pass_http(http_parser_t *parser,
        const char *correctuser, const char *correctpass)
{
    /* This will look something like "Basic QWxhZGRpbjpvcGVuIHNlc2FtZQ==" */
    const char *header = httpp_getvar(parser, "authorization");
    char *userpass, *tmp;
    char *username, *password;

    if(header == NULL)
        return 0;

    if(strncmp(header, "Basic ", 6))
        return 0;

    userpass = util_base64_decode(header+6);
    if(userpass == NULL) {
        WARN1("Base64 decode of Authorization header \"%s\" failed",
                header+6);
        return 0;
    }

    tmp = strchr(userpass, ':');
    if(!tmp) {
        free(userpass);
        return 0;
    }
    *tmp = 0;
    username = userpass;
    password = tmp+1;

    if(strcmp(username, correctuser) || strcmp(password, correctpass)) {
        free(userpass);
        return 0;
    }
    free(userpass);

    return 1;
}

static int _check_pass_icy(http_parser_t *parser, const char *correctpass)
{
    const char *password;

    password = httpp_getvar(parser, HTTPP_VAR_ICYPASSWORD);
    if(!password)
        return 0;

    if (strcmp(password, correctpass))
        return 0;
    else
        return 1;
}

static int _check_pass_ice(http_parser_t *parser, const char *correctpass)
{
    const char *password;

    password = httpp_getvar(parser, "ice-password");
    if(!password)
        password = "";

    if (strcmp(password, correctpass))
        return 0;
    else
        return 1;
}

int connection_check_admin_pass(http_parser_t *parser)
{
    int ret;
    ice_config_t *config = config_get_config();
    char *pass = config->admin_password;
    char *user = config->admin_username;
    const char *protocol;

    if(!pass || !user) {
        config_release_config();
        return 0;
    }

    protocol = httpp_getvar (parser, HTTPP_VAR_PROTOCOL);
    if (protocol && strcmp (protocol, "ICY") == 0)
        ret = _check_pass_icy (parser, pass);
    else
        ret = _check_pass_http (parser, user, pass);
    config_release_config();
    return ret;
}

int connection_check_relay_pass(http_parser_t *parser)
{
    int ret;
    ice_config_t *config = config_get_config();
    char *pass = config->relay_password;
    char *user = config->relay_username;

    if(!pass || !user) {
        config_release_config();
        return 0;
    }

    ret = _check_pass_http(parser, user, pass);
    config_release_config();
    return ret;
}


/* return 0 for failed, 1 for ok
 */
int connection_check_pass (http_parser_t *parser, const char *user, const char *pass)
{
    int ret;
    const char *protocol;

    if(!pass) {
        WARN0("No source password set, rejecting source");
        return -1;
    }

    protocol = httpp_getvar(parser, HTTPP_VAR_PROTOCOL);
    if(protocol != NULL && !strcmp(protocol, "ICY")) {
        ret = _check_pass_icy(parser, pass);
    }
    else {
        ret = _check_pass_http(parser, user, pass);
        if (!ret)
        {
            ice_config_t *config = config_get_config_unlocked();
            if (config->ice_login)
            {
                ret = _check_pass_ice(parser, pass);
                if(ret)
                    WARN0("Source is using deprecated icecast login");
            }
        }
    }
    return ret;
}
/* XXX(xaiki): This may need AUTH support */
static void _handle_post_request (client_t *client, const char *uri)
{
    INFO1("Source logging in at mountpoint \"%s\"", uri);

    source_startup (client, uri, NOAUTH_SOURCE_AUTH);
}

/* only called for native icecast source clients */
static void _handle_source_request (client_t *client, const char *uri)
{
    INFO1("Source logging in at mountpoint \"%s\"", uri);

    if (uri[0] != '/')
    {
        WARN0 ("source mountpoint not starting with /");
        client_send_401 (client);
        return;
    }
    switch (client_check_source_auth (client, uri))
    {
        case 0: /* authenticated from config file */
            source_startup (client, uri, ICECAST_SOURCE_AUTH);
            break;

        case 1: /* auth pending */
            break;

        default: /* failed */
            INFO1("Source (%s) attempted to login with invalid or missing password", uri);
            client_send_401(client);
            break;
    }
}


void source_startup (client_t *client, const char *uri, int auth_style)
{
    source_t *source;
    refbuf_t *ok;
    source = source_reserve (uri);

    if (!source) {
        client_send_403 (client, "Mountpoint in use");
        WARN1 ("Mountpoint %s in use", uri);
        return;
    }

    source->client = client;
    source->parser = client->parser;
    source->con = client->con;
    if (connection_complete_source (source, 1) < 0) {
        source_clear_source (source);
        source_free_source (source);
        return;
    }
    client->respcode = 200;
    switch (auth_style) {
    case SHOUTCAST_SOURCE_AUTH:
        source->shoutcast_compat = 1;
    case NOAUTH_SOURCE_AUTH:
        break;
    case ICECAST_SOURCE_AUTH:
        ok = refbuf_new (PER_CLIENT_REFBUF_SIZE);
        client->respcode = 200;
        snprintf (ok->data, PER_CLIENT_REFBUF_SIZE,
                  "HTTP/1.0 200 OK\r\n\r\n");
        ok->len = strlen (ok->data);
        /* we may have unprocessed data read in, so don't overwrite it */
        ok->associated = client->refbuf;
        client->refbuf = ok;
        break;
    default:
        WARN1("Got unkown source auth type: %d", auth_style);
        return;
    }
    fserve_add_client_callback (client, source_client_callback, source);
}

static void _handle_stats_request (client_t *client, char *uri)
{
    stats_event_inc(NULL, "stats_connections");

    if (connection_check_admin_pass (client->parser) == 0)
    {
        client_send_401 (client);
        ERROR0("Bad password for stats connection");
        return;
    }

    client->respcode = 200;
    snprintf (client->refbuf->data, PER_CLIENT_REFBUF_SIZE,
            "HTTP/1.0 200 OK\r\n\r\n");
    client->refbuf->len = strlen (client->refbuf->data);
    fserve_add_client_callback (client, stats_callback, NULL);
}

static void _handle_get_request (client_t *client, char *passed_uri)
{
    int port;
    char *serverhost = NULL;
    int serverport = 0;
    aliases *alias;
    ice_config_t *config;
    char *uri = passed_uri;
    listener_t *listen_sock;

    config = config_get_config();
    port = config->port;

    listen_sock = config_get_listen_sock (config, client->con);
    if (listen_sock)
    {
        serverhost = listen_sock->bind_address;
        serverport = listen_sock->port;
    }
    alias = config->aliases;

    /* there are several types of HTTP GET clients
    ** media clients, which are looking for a source (eg, URI = /stream.ogg)
    ** stats clients, which are looking for /admin/stats.xml
    ** and directory server authorizers, which are looking for /GUID-xxxxxxxx
    ** (where xxxxxx is the GUID in question) - this isn't implemented yet.
    ** we need to handle the latter two before the former, as the latter two
    ** aren't subject to the limits.
    */
    /* TODO: add GUID-xxxxxx */

    /* Handle aliases */
    while(alias) {
        if(strcmp(uri, alias->source) == 0 && (alias->port == -1 || alias->port == serverport) && (alias->bind_address == NULL || (serverhost != NULL && strcmp(alias->bind_address, serverhost) == 0))) {
            uri = strdup (alias->destination);
            DEBUG2 ("alias has made %s into %s", passed_uri, uri);
            break;
        }
        alias = alias->next;
    }
    config_release_config();

    stats_event_inc(NULL, "client_connections");

    /* Dispatch all admin requests */
    if ((strcmp(uri, "/admin.cgi") == 0) ||
        (strncmp(uri, "/admin/", 7) == 0)) {
        admin_handle_request(client, uri);
        if (uri != passed_uri) free (uri);
        return;
    }
    auth_add_listener (uri, client);
    if (uri != passed_uri) free (uri);
}

static int _handle_shoutcast_stage1 (connection_queue_t *node, char *shoutcast_mount, mount_proxy *mountinfo)
{
    refbuf_t *refbuf = node->refbuf;
    char *source_password;
    int err, passlen;

    WARN ("IN");

    if (mountinfo && mountinfo->password) {
        source_password = strdup (mountinfo->password);
    } else {
        ice_config_t *config = config_get_config ();
        source_password = strdup (config->source_password);
        config_release_config();
    }

    passlen = util_read_header (node->con, refbuf, HEADER_READ_LINE);
    if (passlen <= 0) {
        WARN ("HEADER READ FAILED");
        err = passlen;
        goto out_FAIL;
    }

    if (memmem (refbuf->data, passlen, source_password, strlen(source_password)) == NULL) {
        INFO ("password does not match (%d) \"%s\" (%d) \"%s\"",
              strlen(source_password), source_password, passlen, refbuf->data);
        err = -ENOENT;
        goto out_FAIL;
    }

/* send this non-blocking but if there is only a partial write
 * then leave to header timeout */
    sock_write (node->con->sock, "OK2\r\nicy-caps:11\r\n\r\n");

    WARN ("OK2\r\nicy-caps:11\r\n\r\n");

    refbuf->sync_point = snprintf (refbuf->data, refbuf->len, "POST %s HTTP/1.0\r\n", shoutcast_mount);

    /* we've checked the password, now send it back for reading headers */
    free (source_password);
    return 0;

out_FAIL:
    free (source_password);
    return err;
}

static int _handle_client (client_t *client)
{
    const char *rawuri;
    http_parser_t *parser = client->parser;
    char *uri;

    rawuri = httpp_getvar(parser, HTTPP_VAR_URI);

    if (strcmp("ICE",  httpp_getvar(parser, HTTPP_VAR_PROTOCOL)) &&
        strcmp("HTTP", httpp_getvar(parser, HTTPP_VAR_PROTOCOL))) {
        ERROR0("Bad HTTP protocol detected");
        client_destroy (client);
        return 0;
    }

    uri = util_normalise_uri(rawuri);

    if (uri == NULL)
    {
        client_destroy (client);
        return 0;
    }

    if (parser->req_type == httpp_req_source) {
        _handle_source_request (client, uri);
    }
    else if (parser->req_type == httpp_req_post) {
        _handle_post_request (client, uri);
    }
    else if (parser->req_type == httpp_req_stats) {
        _handle_stats_request (client, uri);
    }
    else if (parser->req_type == httpp_req_get) {
        _handle_get_request (client, uri);
    }
    else {
        ERROR0("Wrong request type from client");
        client_send_400 (client, "unknown request");
    }

    free(uri);
    return 1;
}

/* called when listening thread is not checking for incoming connections */
int connection_setup_sockets (ice_config_t *config)
{
    int count = 0;
    listener_t *listener, **prev;

    free (banned_ip.filename);
    banned_ip.filename = NULL;
    free (allowed_ip.filename);
    allowed_ip.filename = NULL;

    global_lock();
    if (global.serversock)
    {
        for (; count < global.server_sockets; count++)
            sock_close (global.serversock [count]);
        free (global.serversock);
        global.serversock = NULL;
    }
    if (config == NULL)
    {
        global_unlock();
        return 0;
    }

    /* setup the banned/allowed IP filenames from the xml */
    if (config->banfile)
        banned_ip.filename = strdup (config->banfile);

    if (config->allowfile)
        allowed_ip.filename = strdup (config->allowfile);

    count = 0;
    global.serversock = calloc (config->listen_sock_count, sizeof (sock_t));

    listener = config->listen_sock;
    prev = &config->listen_sock;
    while (listener)
    {
        int successful = 0;

        do
        {
            sock_t sock = sock_get_server_socket (listener->port, listener->bind_address);
            if (sock == SOCK_ERROR)
                break;
            if (sock_listen (sock, ICE_LISTEN_QUEUE) == SOCK_ERROR)
            {
                sock_close (sock);
                break;
            }
            /* some win32 setups do not do TCP win scaling well, so allow an override */
            if (listener->so_sndbuf)
                sock_set_send_buffer (sock, listener->so_sndbuf);
            sock_set_blocking (sock, 0);
            successful = 1;
            global.serversock [count] = sock;
            count++;
        } while(0);
        if (successful == 0)
        {
            if (listener->bind_address)
                ERROR2 ("Could not create listener socket on port %d bind %s",
                        listener->port, listener->bind_address);
            else
                ERROR1 ("Could not create listener socket on port %d", listener->port);
            /* remove failed connection */
            *prev = config_clear_listener (listener);
            listener = *prev;
            continue;
        }
        if (listener->bind_address)
            INFO2 ("listener socket on port %d address %s", listener->port, listener->bind_address);
        else
            INFO1 ("listener socket on port %d", listener->port);
        prev = &listener->next;
        listener = listener->next;
    }
    global.server_sockets = count;
    global_unlock();

    if (count == 0)
        ERROR0 ("No listening sockets established");

    return count;
}


void connection_close(connection_t *con)
{
    sock_close(con->sock);
    if (con->ip) free(con->ip);
    if (con->host) free(con->host);
#ifdef HAVE_OPENSSL
    if (con->ssl) { SSL_shutdown (con->ssl); SSL_free (con->ssl); }
#endif
    free(con);
}
