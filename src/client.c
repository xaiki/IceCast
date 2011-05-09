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

/* client.c
**
** client interface implementation
**
*/

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <string.h>

#include "thread/thread.h"
#include "avl/avl.h"
#include "httpp/httpp.h"

#include "cfgfile.h"
#include "connection.h"
#include "refbuf.h"
#include "format.h"
#include "stats.h"
#include "fserve.h"
#include "util.h"
#include "amalloc.h"

#include "client.h"
#include "logging.h"

#ifdef _WIN32
#define snprintf _snprintf
#endif

#undef CATMODULE
#define CATMODULE "client"

/* create a client_t with the provided connection and parser details. Return
 * 0 on success, -1 if server limit has been reached.  In either case a
 * client_t is returned just in case a message needs to be returned. Should
 * be called with global lock held.
 */
int client_create (client_t **c_ptr, connection_t *con, http_parser_t *parser)
{
    ice_config_t *config;
    client_t *client = (client_t *)acalloc(1, sizeof(client_t));
    const char *transferenc;
    int ret = 0;

    transferenc = httpp_getvar (parser, "transfer-encoding");

    client->con = con;
    client->parser = parser;
    client->refbuf = refbuf_new (PER_CLIENT_REFBUF_SIZE);
    client->refbuf->len = 0; /* force reader code to ignore buffer contents */
    client->pos = 0;
    client->write_to_client = format_generic_write_to_client;

    *c_ptr = client;

    if (transferenc && (! strcmp ("chunked", transferenc))) {
        client->chunksize = 0;
    } else {
        client->chunksize = -1;
    }

	WARN("<xaiki> Created client client: %p. con=%p, fd=%d, chunked=%d, %s",
         client, con, con->sock, client->chunksize, transferenc);

    config = config_get_config ();
    global.clients++;
    if (config->client_limit < global.clients) {
        /* don't be too eager as this is an imposed hard limit */
        client_send_403 (client, "Icecast connection limit reached");
        ret = -EINPROGRESS;
    }

    config_release_config ();
    stats_event_args (NULL, "clients", "%d", global.clients);

    return ret;
}

void client_destroy(client_t *client)
{
    if (client == NULL)
        return;

    /* release the buffer now, as the buffer could be on the source queue
     * and may of disappeared after auth completes */
    if (client->refbuf)
    {
        refbuf_release (client->refbuf);
        client->refbuf = NULL;
    }

    if (auth_release_listener (client))
        return;

    /* write log entry if ip is set (some things don't set it, like outgoing
     * slave requests
     */
    if (client->respcode && client->parser)
        logging_access(client);

    if (client->con)
        connection_close(client->con);
    if (client->parser)
        httpp_destroy(client->parser);

    global_lock ();
    global.clients--;
    stats_event_args (NULL, "clients", "%d", global.clients);
    global_unlock ();

    /* we need to free client specific format data (if any) */
    if (client->free_client_data)
        client->free_client_data (client);

    free(client->username);
    free(client->password);

    free(client);
}

/* return -1 for failed, 0 for authenticated, 1 for pending
 */
int client_check_source_auth (client_t *client, const char *mount)
{
    ice_config_t *config = config_get_config();
    char *pass = config->source_password;
    char *user = "source";
    int ret = -1;
    mount_proxy *mountinfo = config_find_mount (config, mount);

    do
    {
        if (mountinfo)
        {
            ret = 1;
            if (auth_stream_authenticate (client, mount, mountinfo) > 0)
                break;
            ret = -1;
            if (mountinfo->password)
                pass = mountinfo->password;
            if (mountinfo->username)
                user = mountinfo->username;
        }
        if (connection_check_pass (client->parser, user, pass) > 0)
            ret = 0;
    } while (0);
    config_release_config();
    return ret;
}

static int client_getc(client_t *client) {
    refbuf_t *refbuf = client->refbuf;
	int len;
	char b;

	if (client->refbuf && client->refbuf->len < client->refbuf->sync_point)
		return *(refbuf->data + refbuf->sync_point++);
	len = client->con->read (client->con, &b, 1);

    if (len <= 0)
        return -EIO;
    if (len == 0)
        return -1;

    return b;
}

static int client_get_line(client_t *client, char *line, int line_size) {
    int ch;
    char *q;

    q = line;
    for(;;) {
        ch = client_getc(client);
        if (ch < 0)
            return -1;
        if (ch == '\n') {
            /* process line */
            if (q > line && q[-1] == '\r')
                q--;
            *q = '\0';

            return 0;
        } else {
            if ((q - line) < line_size - 1)
                *q++ = ch;
        }
    }
}

/* helper function for reading data from a client */
int client_read_bytes (client_t *client, void *buf, int len)
{
    refbuf_t *refbuf = client->refbuf;

    if (client->chunksize >= 0) {
	    if (!client->chunksize) {
		    char line[32];

			for(;;) {
				do {
					if (client_get_line(client, line, sizeof(line)) < 0)
						return -1;

                } while (!*line);    /* skip CR LF from last chunk */

                client->chunksize = strtoll(line, NULL, 16);

                DEBUG ("Chunked encoding data size: %d (%x)\n", client->chunksize, client->chunksize);

                if (!client->chunksize)
                    return 0;
                break;
            }
        }
        len = MIN(len, client->chunksize);
    }

    if (client->refbuf && client->refbuf->len)
    {
        /* we have data to read from a refbuf first */
        if (refbuf->len - refbuf->sync_point < len)
            len = refbuf->len - refbuf->sync_point;
        memcpy (buf, refbuf->data + refbuf->sync_point, len);
        if (len < refbuf->len - refbuf->sync_point)
        {
            char *ptr = client->refbuf->data + refbuf->sync_point;
            memmove (ptr, ptr+len, client->refbuf->len - refbuf->sync_point - len);
        }
        refbuf->len -= len;
    } else {
        len = client->con->read (client->con, buf, len);
    }

    if (len <= 0) {
        if (len == -1 && client->con->error)
            DEBUG0 ("reading from connection has failed");
    } else  {
        if (client->chunksize > 0)
            client->chunksize -= len;
    }
    return len;
}


void client_send_400(client_t *client, char *message) {
    ERROR("400 -> %s", message);
    snprintf (client->refbuf->data, PER_CLIENT_REFBUF_SIZE,
            "HTTP/1.0 400 Bad Request\r\n"
            "Content-Type: text/html\r\n\r\n"
            "<b>%s</b>\r\n", message);
    client->respcode = 400;
    client->refbuf->len = strlen (client->refbuf->data);
    fserve_add_client (client, NULL);
}

void client_send_404(client_t *client, char *message) {

    snprintf (client->refbuf->data, PER_CLIENT_REFBUF_SIZE,
            "HTTP/1.0 404 File Not Found\r\n"
            "Content-Type: text/html\r\n\r\n"
            "<b>%s</b>\r\n", message);
    client->respcode = 404;
    client->refbuf->len = strlen (client->refbuf->data);
    fserve_add_client (client, NULL);
}


void client_send_401(client_t *client) {
    snprintf (client->refbuf->data, PER_CLIENT_REFBUF_SIZE,
            "HTTP/1.0 401 Authentication Required\r\n"
            "WWW-Authenticate: Basic realm=\"Icecast2 Server\"\r\n"
            "\r\n"
            "You need to authenticate\r\n");
    client->respcode = 401;
    client->refbuf->len = strlen (client->refbuf->data);
    fserve_add_client (client, NULL);
}

void client_send_403(client_t *client, const char *reason)
{
    if (reason == NULL)
        reason = "Forbidden";
    snprintf (client->refbuf->data, PER_CLIENT_REFBUF_SIZE,
            "HTTP/1.0 403 %s\r\n\r\n", reason);
    client->respcode = 403;
    client->refbuf->len = strlen (client->refbuf->data);
    fserve_add_client (client, NULL);
    DEBUG ("Sending 403: %s", reason);
}


/* helper function for sending the data to a client */
int client_send_bytes (client_t *client, const void *buf, unsigned len)
{
    int ret = client->con->send (client->con, buf, len);

    if (client->con->error)
        DEBUG0 ("Client connection died");

    return ret;
}

void client_set_queue (client_t *client, refbuf_t *refbuf)
{
    refbuf_t *to_release = client->refbuf;

    client->refbuf = refbuf;
    if (refbuf)
        refbuf_addref (client->refbuf);
    client->pos = 0;
    if (to_release)
        refbuf_release (to_release);
}

