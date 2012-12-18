/* passfs Customized for Palm webOS
   Made from Palm patches and snippets of CryptoFS source.
   (C)2012 Yukai Li
   (C)2009-2012 Palm, Inc. / Hewlett-Packard Development Company, L.P.
   CryptoFS source and Palm patch can be found at http://opensource.palm.com/3.0.5/index.html
*/

/*
This code uses code written by Radek Podgorny for his unionfs-fuse as a template It retains his stats,debug and opts modules as useful service routines and follows his startup structure.

The initial aim is to produce a more useful template than the xmpl code that comes with the FUSE package. The template just acts as a pass through fileing system. you just give it 
a directory and it treats that as the root of a fileing system. Not intrinsically very useful. However the code demonstrates the use of some of the parameter
analysis interfaces and can be used as a simple monitor.

John Cobb

Written by Radek Podgorny

This is offered under a BSD-style license. This means you can use the code for whatever you desire in any way you may want but you MUST NOT forget to give me appropriate credits when spreading your work which is based on mine. Something like "original implementation by Radek Podgorny" should be fine.
*/
#include "fsname.h"
#ifdef linux
	/* For pread()/pwrite() */
	#define _XOPEN_SOURCE 500
#endif

#include <fuse.h>

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <unistd.h>
#include <fcntl.h>
#include <dirent.h>
#include <errno.h>
#include <signal.h>
#include <syslog.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <pthread.h>

#include <glib.h>
#include <assert.h>
#ifdef HAVE_SETXATTR
	#include <sys/xattr.h>
#endif

#ifdef F_FULLFSYNC
/* this is a Mac OS X system which does not implement fdatasync as such */
#define fdatasync(f) fcntl(f, F_FULLFSYNC)
#endif

#include "userModeFS.h"

#include "stats.h"
#include "debug.h"
int monitor=0;
FILE *monitor_file=NULL;

#define MSM_STATE_NONE    0
#define MSM_STATE_ENTER   1
#define MSM_STATE_EXIT    2
#define MSM_STATE_MSM     3
static sig_atomic_t msm_state = MSM_STATE_NONE;
static pthread_t msm_thread;

struct file_info {
	char *name;
	int fd;
	int flags;
	int refcnt;
};

struct dir_info {
	char *name;
	DIR *dir;
	int refcnt;
};

static pthread_mutex_t s_file_table_mutex;
static pthread_mutex_t s_dir_table_mutex;

static GHashTable *s_file_table;
static GHashTable *s_dir_table;

// #define MUTEX_DEBUG
#ifdef MUTEX_DEBUG

static gboolean s_have_file_mutex = FALSE;
static gboolean s_have_dir_mutex = FALSE;

# define WITH_MUTEX(m,b) {                           \
    pthread_mutex_t* const _mp = &(m);               \
    gboolean* const _bp = &(b);                      \
	int _res = pthread_mutex_lock( _mp );            \
    assert( 0 == _res );                             \
    assert( !*_bp );                                 \
    *_bp = TRUE

# define WITH_MUTEX_FILE() WITH_MUTEX( s_file_table_mutex, s_have_file_mutex )
# define WITH_MUTEX_DIR() WITH_MUTEX( s_dir_table_mutex, s_have_dir_mutex )

# define END_WITH_MUTEX()                            \
    assert( *_bp );                                  \
    *_bp = FALSE;                                    \
	_res = pthread_mutex_unlock(_mp);                \
    assert( 0 == _res );                             \
}

# define ASSERT_LOCKED_FILE() assert( s_have_file_mutex );
# define ASSERT_LOCKED_DIR() assert( s_have_dir_mutex );

#else

# define WITH_MUTEX(m) {                        \
    pthread_mutex_t* _mp = &(m);                \
	pthread_mutex_lock(_mp)

# define END_WITH_MUTEX() pthread_mutex_unlock(_mp); }

# define WITH_MUTEX_FILE() WITH_MUTEX( s_file_table_mutex )
# define WITH_MUTEX_DIR() WITH_MUTEX( s_dir_table_mutex )

# define ASSERT_LOCKED_DIR()
# define ASSERT_LOCKED_FILE()

#endif

#define NDEBUG
//#undef NDEBUG

#ifndef NDEBUG
#define TRACE_ENTRY    syslog(LOG_DEBUG, "%s: entry msm %d\n", __func__, msm_state)
#define DEBUG_RETURN(x) { syslog(LOG_DEBUG, "%s()=>%d\n", __func__, x ); return (x); }
#define DEBUGF(x...)    syslog(LOG_DEBUG, x)
#else
#define TRACE_ENTRY
#define DEBUG_RETURN(x) return (x)
#define DEBUGF(x...)
#endif

static void file_table_put(char *path, int fd, int flags)
{
	struct file_info *info;
	DEBUGF("%s: path %s fd %d flags 0x%08x\n", __func__, path, fd, flags);

    WITH_MUTEX_FILE();

    assert( MSM_STATE_NONE == msm_state );

	if ((info = (struct file_info *)g_hash_table_lookup(s_file_table, path)) != NULL) {
		info->refcnt += 1;
		syslog(LOG_ERR, "%s: path %s exists in file table\n", __func__,
				path);
		close(fd);
	} else {
		info = g_malloc0(sizeof(struct file_info));
		info->name = path;
		info->fd = fd;
		info->flags = flags;
		info->refcnt = 1;
		g_hash_table_insert(s_file_table, path, (gpointer)info);
	}

    END_WITH_MUTEX();
}

static struct file_info * file_table_get(const char *path)
{
	struct file_info *info;

    WITH_MUTEX_FILE();
    assert( MSM_STATE_NONE == msm_state );
	info = (struct file_info *)g_hash_table_lookup(s_file_table, path);

	if (info != NULL) {
		DEBUGF("%s: path %s fd %d flags 0x%08x\n", __func__, path,
				info->fd, info->flags);
	} else {
		DEBUGF("%s: path %s not found\n", __func__, path);
	}
    END_WITH_MUTEX();

	return info;
}

static struct file_info * file_table_get_refinc(const char *path)
{
	struct file_info *info;

    WITH_MUTEX_FILE();
    assert( MSM_STATE_NONE == msm_state );
	info = (struct file_info *)g_hash_table_lookup(s_file_table, path);

	if (info != NULL) {
		DEBUGF("%s: path %s fd %d flags 0x%08x refcnt %d\n", __func__, path,
				info->fd, info->flags, info->refcnt);
		info->refcnt += 1;
	} else {
		DEBUGF("%s: path %s not found\n", __func__, path);
	}
    END_WITH_MUTEX();

	return info;
}

static int file_table_del(const char *path)
{
	int rc = 0;
	struct file_info *info;

    WITH_MUTEX_FILE();
    assert( MSM_STATE_NONE == msm_state );
	info = (struct file_info *)g_hash_table_lookup(s_file_table, path);
	if (info != NULL) {
		info->refcnt -= 1;
		DEBUGF("%s: path %s refcnt %d\n", __func__, path, info->refcnt);
		if (info->refcnt == 0) {
			g_hash_table_remove(s_file_table, path);
			g_free(info->name);
			g_free(info);
			rc = 1;
		}
	}
    END_WITH_MUTEX();
	return rc;
}

static void dir_table_put(char *path, DIR *dir)
{
	struct dir_info *info;
	DEBUGF("%s: path %s dir %p\n", __func__, path, dir);

    WITH_MUTEX_DIR();
    assert( MSM_STATE_NONE == msm_state );
	if ((info = (struct dir_info *)g_hash_table_lookup(s_dir_table, path)) != NULL) {
		info->refcnt += 1;
		syslog(LOG_ERR, "%s: path %s exists in dir table\n", __func__, path);
		closedir(dir);
	} else {
		info = g_malloc0(sizeof(struct dir_info));
		info->name = path;
		info->dir = dir;
		info->refcnt = 1;
		g_hash_table_insert(s_dir_table, path, (gpointer)info);
	}

    END_WITH_MUTEX();
}

static struct dir_info * dir_table_get(const char *path)
{
	struct dir_info *info;

    WITH_MUTEX_DIR();
    assert( MSM_STATE_NONE == msm_state );
	info = g_hash_table_lookup(s_dir_table, path);
	if (info != NULL) {
		DEBUGF("%s: path %s dir %p\n", __func__, path, info->dir);
	} else {
		DEBUGF("%s: path %s not found\n", __func__, path);
	}
    END_WITH_MUTEX();

	return info;
}

static struct dir_info * dir_table_get_refinc(const char *path)
{
	struct dir_info *info;

    WITH_MUTEX_DIR();
    assert( MSM_STATE_NONE == msm_state );
	info = (struct dir_info *)g_hash_table_lookup(s_dir_table, path);
	if (info != NULL) {
		DEBUGF("%s: path %s dir %p\n", __func__, path, info->dir);
		info->refcnt += 1;
	} else {
		DEBUGF("%s: path %s not found\n", __func__, path);
	}
    END_WITH_MUTEX();

	return info;
}

static int dir_table_del(const char *path)
{
	int rc = 0;
	struct dir_info *info;

    WITH_MUTEX_DIR();
    assert( MSM_STATE_NONE == msm_state );
	info = (struct dir_info *)g_hash_table_lookup(s_dir_table, path);
	if (info != NULL) {
		info->refcnt -= 1;
		DEBUGF("%s: path %s refcnt %d\n", __func__, path, info->refcnt);
		if (info->refcnt == 0) {
			g_hash_table_remove(s_dir_table, path);
			g_free(info->name);
			g_free(info);
			rc = 1;
		}
	}
    END_WITH_MUTEX();
	return rc;
}

static void do_close_fd(gpointer data, gpointer user_data)
{
	char *key = data;
    ASSERT_LOCKED_FILE();
	struct file_info *info =
		(struct file_info *)g_hash_table_lookup(s_file_table, key);

	if (info == NULL) {
		DEBUGF("%s: path %s not found\n", __func__, key);
		return;
	}

	DEBUGF("closing fd %s %d\n", key, info->fd);
	close(info->fd);
}

static void do_open_fd(gpointer data, gpointer user_data)
{
    ASSERT_LOCKED_FILE();
	char *key = data;
	struct file_info *info =
		(struct file_info *)g_hash_table_lookup(s_file_table, key);

	if (info == NULL) {
		DEBUGF("%s: path %s not found\n", __func__, key);
		return;
	}

    info->fd = open(key, info->flags);
	DEBUGF("opening fd %s flags %d -> %d\n", key, info->flags, info->fd);
}

static void do_close_dir(gpointer data, gpointer user_data)
{
	char *key = data;
    ASSERT_LOCKED_DIR();
	struct dir_info *info = g_hash_table_lookup(s_dir_table, key);

	if (info == NULL) {
		DEBUGF("%s: path %s not found\n", __func__, key);
		return;
	}

	DEBUGF("closing dir %s\n", key);
	closedir(info->dir);
}

static void do_open_dir(gpointer data, gpointer user_data)
{
	char *key = data;
    ASSERT_LOCKED_DIR();
	struct dir_info *info = g_hash_table_lookup(s_dir_table, key);

	if (info == NULL) {
		DEBUGF("%s: path %s not found\n", __func__, key);
		return;
	}

	info->dir = opendir(key);
	DEBUGF("opening dir %s -> %p\n", key, info->dir);
}

static void msm_enter_handler(void)
{
	GList *keys;
    ASSERT_LOCKED_DIR();
    ASSERT_LOCKED_FILE();

	keys = g_hash_table_get_keys(s_file_table);
	g_list_foreach(keys, do_close_fd, NULL);
	g_list_free(keys);

	keys = g_hash_table_get_keys(s_dir_table);
	g_list_foreach(keys, do_close_dir, NULL);
	g_list_free(keys);
}

static void msm_exit_handler(void)
{
	GList *keys;
    ASSERT_LOCKED_DIR();
    ASSERT_LOCKED_FILE();

	keys = g_hash_table_get_keys(s_file_table);
	g_list_foreach(keys, do_open_fd, NULL);
	g_list_free(keys);

	keys = g_hash_table_get_keys(s_dir_table);
	g_list_foreach(keys, do_open_dir, NULL);
	g_list_free(keys);
}

static void *msm_handler(void *arg)
{
	sigset_t set;
	int sig;

	DEBUGF("%s", "enter msm handler thread\n");

	sigemptyset(&set);
	sigaddset(&set, SIGUSR1);
	sigaddset(&set, SIGUSR2);

	for (;;) {
		DEBUGF("%s", "waiting...\n");

		if (sigwait(&set, &sig) != 0) {
			syslog(LOG_ERR, "error waiting for msm signal\n");
			continue;
		}

		DEBUGF("received signal %d\n", sig);

		switch (sig) {
			case SIGUSR1:
				syslog(LOG_INFO, "msm enter\n");
                WITH_MUTEX_DIR();
                WITH_MUTEX_FILE();
				msm_state = MSM_STATE_ENTER;
				msm_enter_handler();
				msm_state = MSM_STATE_MSM;
                END_WITH_MUTEX();
                END_WITH_MUTEX();
				break;
			case SIGUSR2:
				syslog(LOG_INFO, "msm exit\n");
                WITH_MUTEX_DIR();
                WITH_MUTEX_FILE();
				msm_state = MSM_STATE_EXIT;
				msm_exit_handler();
				msm_state = MSM_STATE_NONE;
                END_WITH_MUTEX();
                END_WITH_MUTEX();
				break;
			default:
				syslog(LOG_INFO, "unknown signal %d\n", sig);
				break;
		}
	}

	return NULL;
}

gchar *make_gchar(const char *str) {
	GString *ret;
	gchar *retstr;

	ret = g_string_new(str);
	retstr = ret->str;
	g_string_free(ret, FALSE);

	return retstr;
}

static void * userModeFS_init(struct fuse_conn_info *conn)
{
	TRACE_ENTRY;

	if (pthread_create(&msm_thread, NULL, msm_handler, NULL) < 0) {
		syslog(LOG_ERR, "error creating msm thread\n");
	}

	return NULL;
}

static void mprintf(const char *format,...) {

	va_list vp;
	
	if(monitor&2){va_start(vp,format);vfprintf(stdout,format,vp);va_end(vp);}
	if(monitor_file){va_start(vp,format);vfprintf(monitor_file,format,vp);va_end(vp);}
}
int monitorInit(const char *file)
{

	if(file){
		monitor_file=fopen(file,"w");
		if(monitor_file)monitor|=1;
		else return 1;
	}
	else {
		monitor|=2;
	}
	return 0;
}
static int userModeFS_access(const char *path, int mask) {
	DBG("access\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("access %s,mask=%x",path,mask);
	int res = access(p, mask);
	if (res == -1) {
		if(monitor)mprintf(" res=%x\n",errno);
		DEBUG_RETURN( -errno );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_chmod(const char *path, mode_t mode) {
	DBG("chmod\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("chmod %s,mode=%x",path,mode);
	int res = chmod(p, mode);
	if (res == -1) {
		if(monitor)mprintf(" res=%x\n",errno);
		DEBUG_RETURN( -errno );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_chown(const char *path, uid_t uid, gid_t gid) {
	DBG("chown\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("chown %s,uid=%x,gid=%x",path,uid,gid);
	int res = lchown(p, uid, gid);
	if (res == -1) {
			if(monitor)mprintf(" res=%x\n",errno);
			DEBUG_RETURN( -errno );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

/* flush may be called multiple times for an open file, this must not really close the file. This is important if used on a network filesystem like NFS which flush the data/metadata on close() */
static int userModeFS_flush(const char *path, struct fuse_file_info *fi) {
	struct file_info *info;
	char *cpath = (char *) fi->fh;

	DBG("flush\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	if (stats_enabled && strcmp(path, STATS_FILENAME) == 0) return 0;

	info = file_table_get(cpath);
	if (info == NULL) {
        DEBUG_RETURN( -EIO );
	}

	int fd = dup(info->fd);
	if(monitor)mprintf("flush %s",path);
	if (fd == -1) {
		// What to do now?
		if (fsync(info->fd) == -1) {
			if(monitor)mprintf(" res=%x\n",EIO);
			DEBUG_RETURN( -EIO );
		}
		if(monitor)mprintf(" res=FAIL\n");
		return 0;
	}

	if (close(fd) == -1){
		if(monitor)mprintf(" res=%x\n",errno);
		DEBUG_RETURN( -errno );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

/* Just a stub. This method is optional and can safely be left unimplemented */
static int userModeFS_fsync(const char *path, int isdatasync, struct fuse_file_info *fi) {
	struct file_info *info;
	char *cpath = (char *) fi->fh;

	DBG("fsync\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	if (stats_enabled && strcmp(path, STATS_FILENAME) == 0) return 0;

	info = file_table_get(cpath);
	if (info == NULL) {
        DEBUG_RETURN( -EIO );
	}

	int res;
	if(monitor)mprintf("fsync %s, isdata",path,isdatasync);
	if (isdatasync) {
		res = fdatasync(info->fd);
	} else {
		res = fsync(info->fd);
	}

	if (res == -1) {
		if(monitor)mprintf(" res=%x\n",errno);
		DEBUG_RETURN( -errno );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_getattr(const char *path, struct stat *stbuf) {
	DBG("getattr\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	if (stats_enabled && strcmp(path, STATS_FILENAME) == 0) {
		memset(stbuf, 0, sizeof(stbuf));
		stbuf->st_mode = S_IFREG | 0444;
		stbuf->st_nlink = 1;
		stbuf->st_size = STATS_SIZE;
		return 0;
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("getattr %s",path);
	int res = lstat(p, stbuf);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN ( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}


static int userModeFS_link(const char *from, const char *to) {
	DBG("link\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char t[PATHLEN_MAX],p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, from);
	snprintf(t, PATHLEN_MAX, "%s%s", root, to);
	if(monitor)mprintf("link from:%s, to:%s",from,to);
	int res = link(p, t);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_mkdir(const char *path, mode_t mode) {
	DBG("mkdir\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);

	if(monitor)mprintf("make dir: %s,mode=%x",path,mode);
	int res = mkdir(p, mode);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_mknod(const char *path, mode_t mode, dev_t rdev) {
	DBG("mknod\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("make node: %s, mode=%x, dev=%x",path,mode,rdev);
    #ifdef __APPLE__
    #warning "Substituting creat for mknod - limited functionality"
    int res = creat(p, mode);
    #else
	int res = mknod(p, mode, rdev);
    #endif
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_open(const char *path, struct fuse_file_info *fi) {
	struct file_info *info;

	DBG("open\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	if(monitor)mprintf("open: %s,flags=%x,",path,fi->flags);
	if (stats_enabled && strcmp(path, STATS_FILENAME) == 0) {
		if ((fi->flags & 3) == O_RDONLY) {
			fi->direct_io = 1;
		}
		else {
			if(monitor)mprintf(" res=%x\n",EACCES);
			return -EACCES;
		}
	}
	else {
		char p[PATHLEN_MAX];
		snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	
		info = file_table_get_refinc(path);
		DEBUGF("%s: open %s info %p\n", __func__, path, info);
		if (info == NULL) {
			// Note: in Palm's source it states "O_APPEND and lseek() don't go together" and O_APPEND is unset from the flags. Ignoring that.
			int fd = open(p, fi->flags);
			if (fd == -1) {
				int res=errno;
				syslog(LOG_CRIT, "%s: path %s err %d (%s)\n", __func__,
						path, res, strerror(errno));
				if(monitor)mprintf(" res=%x\n",res);
				DEBUG_RETURN( -res );
			}
			else {
				gchar *persistpath;
				fi->direct_io = 1;

				DEBUGF("%s: open %s fd %d\n", __func__, path, fd);

				persistpath = make_gchar(p);
				file_table_put(persistpath, fd, fi->flags);
				fi->fh = (unsigned long) persistpath;
			}
		} else {
			fi->fh = (unsigned long)info->name;
		}
	}
	fi->keep_cache = 1;
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_read(const char *path, char *buf, size_t size, off_t offset, struct fuse_file_info *fi) {
	struct file_info *info;
	char *cpath = (char *) fi->fh;

	DBG("read\n");

	DEBUGF("%s: path %s buf %p size %zd off %d cpath %p\n", __func__,
			path, buf, size, offset, cpath);

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}


	if (stats_enabled && strcmp(path, STATS_FILENAME) == 0) {
		char out[STATS_SIZE] = "";
		stats_sprint(out);

		int s = size;
		if (offset < strlen(out)) {
			if (s > strlen(out)-offset) s = strlen(out)-offset;
			memcpy(buf, out+offset, s);
		} else {
			s = 0;
		}
		return s;
	}


	info = file_table_get(cpath);
	if (info == NULL) {
		DEBUGF("%s: fd not found\n", __func__);
        DEBUG_RETURN( -EIO );
	}

	int res = pread(info->fd, buf, size, offset);
	if (res == -1) {
		res = -errno;

		if (res < 0) {
			syslog(LOG_DEBUG, "%s: path %s (%s) res %d (%s)\n", __func__,
					path, cpath, res, strerror(errno));
		}
	}

	if (stats_enabled) stats_add_read(size);

	return res;
}

static int userModeFS_opendir(const char* path, struct fuse_file_info *fi)
{
	struct dir_info *info;

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	info = dir_table_get_refinc(path);
	if (info == NULL) {
		gchar *persistpath;
		char p[PATHLEN_MAX];
		snprintf(p, PATHLEN_MAX, "%s%s", root, path);
		DIR *dp = opendir(p);
		if (dp == NULL) {
			syslog(LOG_DEBUG, "%s: path %s err %d (%s)\n", __func__,
					path, errno, strerror(errno));
            DEBUG_RETURN( -errno );
		}

		persistpath = make_gchar(p);
		dir_table_put(persistpath, dp);

		fi->fh = (unsigned long) persistpath;
	} else {
		fi->fh = (unsigned long)info->name;
	}
    return 0;
}
static int userModeFS_readdirMethod1(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info *fi) {
	char *cpath = (char *) fi->fh;
	struct dir_info *info;

	DBG("readdir\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	info = dir_table_get(cpath);
	if (info == NULL) {
        DEBUG_RETURN( -EIO );
	}

	if (stats_enabled && strcmp(path, "/") == 0) {
		filler(buf, "stats", NULL, 0);
	}

	if(monitor)mprintf("readdir1 %s",path);
	// Note: To readdir() you must have opendir() previously.
	DIR *dp = info->dir;
	if (dp){
		struct dirent *de;
		while ((de = readdir(dp)) != NULL) {
			if (filler(buf, de->d_name, NULL, 0)) break;
		}
	}

	if(monitor)mprintf(" res=OK\n");
	return 0;
}
static int userModeFS_readdirMethod2(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info *fi) {
	char *cpath = (char *) fi->fh;
	struct dir_info *info;

	DBG("readdir\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	info = dir_table_get(cpath);
	if (info == NULL) {
        DEBUG_RETURN( -EIO );
	}

	if(monitor)mprintf("readdir2 %s",path);
	// Note: To readdir() you must have opendir() previously.
	DIR *dp = info->dir;
	if (dp){
		struct dirent *de;
		if(offset)seekdir(dp,offset);
		while ((de = readdir(dp)) != NULL) {
			if (filler(buf, de->d_name, NULL, telldir(dp))) break;
		}
	}
	if (stats_enabled && strcmp(path, "/") == 0) {
		filler(buf, "stats", NULL, 0);
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}
static int userModeFS_releasedir(const char *path, struct fuse_file_info *fi)
{
	int rc;
	char *cpath = (char *) fi->fh;
	struct dir_info *info;
	DIR *dir;

	TRACE_ENTRY;

    (void) path;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	info = dir_table_get(cpath);
	if (info == NULL) {
        DEBUG_RETURN( -EIO );
	}

	dir = info->dir;

	rc = dir_table_del(cpath);
	if (rc) {
		DEBUGF("%s: closing %p\n", __func__, dir);
		closedir(dir);
	}
    return 0;
}
static int userModeFS_readlink(const char *path, char *buf, size_t size) {
	DBG("readlink\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("readlink: %s",path);
	int res = readlink(p, buf, size - 1);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}

	buf[res] = '\0';
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_release(const char *path, struct fuse_file_info *fi) {
	int rc;
	struct file_info *info;
	int fd;
	char *cpath = (char *) fi->fh;

	DBG("release\n");

	DEBUGF("%s: close %s (%s)\n", __func__, path, cpath);

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	if (stats_enabled && strcmp(path, STATS_FILENAME) == 0) return 0;

	info = file_table_get(cpath);
	if (info == NULL) {
        DEBUG_RETURN( -EIO );
	}

	fd = info->fd;
	rc = file_table_del(cpath);
	if (rc) {
		int res;
		DEBUGF("%s: closing %d\n", __func__, fd);
		if(monitor)mprintf("release(close): %s",path);
		res = close(fd);
		if (res == -1) {
			res=errno;
			if(monitor)mprintf(" res=%x\n",res);
			DEBUG_RETURN( -res );
		}
		if(monitor)mprintf(" res=OK\n");
	}
	return 0;
}

static int userModeFS_rename(const char *from, const char *to) {
	DBG("rename\n");

	char f[PATHLEN_MAX];
	snprintf(f, PATHLEN_MAX, "%s%s", root, from);

	char t[PATHLEN_MAX];
	snprintf(t, PATHLEN_MAX, "%s%s", root, to);
	if(monitor)mprintf("rename from:%s, to:%s",from,to);
	int res = rename(f, t);
	if (res == 0) {           /* rename succeeded? */
		/* Now we need to check if we have a mapping for the from file.  If we do,
		   we need to move that as well.  See NOV-93017 */
		struct file_info* info = file_table_get( f );
		if ( info != NULL ) {
		    file_table_put( make_gchar(t), info->fd, info->flags );
		    file_table_del( f );
		}
	} else if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}

	// The path should no longer exist
	
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_rmdir(const char *path) {
	DBG("rmdir\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("rmdir: %s",path);
	int res = rmdir(p);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}

	// The path should no longer exist
	
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_statfs(const char *path, struct statvfs *stbuf) {
	(void)path;

	DBG("statfs\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	if(monitor)mprintf("statfs: %s",path);
	int res = statvfs(root, stbuf);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}


	stbuf->f_fsid = 0;
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_symlink(const char *from, const char *to) {
	DBG("symlink\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char t[PATHLEN_MAX];
	snprintf(t, PATHLEN_MAX, "%s%s", root, to);
	if(monitor)mprintf("symlink from:%s, to:%s",from,to);
	int res = symlink(from, t);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_truncate(const char *path, off_t size) {
	DBG("truncate\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("truncate: %s",path);
	int res = truncate(p, size);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_unlink(const char *path) {
	DBG("unlink\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("unlink: %s",path);
	int res = unlink(p);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}

	// The path should no longer exist

	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_utime(const char *path, struct utimbuf *buf) {
	DBG("utime\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	if (stats_enabled && strcmp(path, STATS_FILENAME) == 0) return 0;

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("utime: %s",path);
	int res = utime(p, buf);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_write(const char *path, const char *buf, size_t size, off_t offset, struct fuse_file_info *fi) {
	int res;
	struct file_info *info;
	char *cpath = (char *) fi->fh;
	errno = 0;                  /* since we'll print it later */

	DBG("write\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	(void)path;

	info = file_table_get(cpath);
	if (info == NULL) {
        DEBUG_RETURN( -EIO );
	}
 
	res = pwrite(info->fd, buf, size, offset);
	if (res == -1) {
		syslog(LOG_DEBUG, "%s: path %s (%s) res %d (%s)\n", __func__,
				path, cpath, res, strerror(errno));
		res = -errno;
	}

	if (stats_enabled && res != -errno) stats_add_written(size);

	DEBUGF("%s: path %s fd %d buf %p size %zd off %d res %d errno %d\n",
			__func__,
			path, info->fd, buf, size, offset, res, errno);

	return res;
}

#ifdef HAVE_SETXATTR
static int userModeFS_getxattr(const char *path, const char *name, char *value, size_t size) {
	DBG("getxattr\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("getxattr: %s",path);
	int res = lgetxattr(p, name, value, size);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_listxattr(const char *path, char *list, size_t size) {
	DBG("listxattr\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("listxattr: %s",path);
	int res = llistxattr(p, list, size);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_removexattr(const char *path, const char *name) {
	DBG("removexattr\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("removexattr: %s,name=%s",path,name);
	int res = lremovexattr(p, name);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}

static int userModeFS_setxattr(const char *path, const char *name, const char *value, size_t size, int flags) {
	DBG("sexattr\n");

	TRACE_ENTRY;

	if (msm_state != MSM_STATE_NONE) {
        DEBUG_RETURN( -EAGAIN );
	}

	char p[PATHLEN_MAX];
	snprintf(p, PATHLEN_MAX, "%s%s", root, path);
	if(monitor)mprintf("setxattr: %s,name=%s,value=%s",path,name,value);
	int res = lsetxattr(p, name, value, size, flags);
	if (res == -1) {
		res=errno;
		if(monitor)mprintf(" res=%x\n",res);
		DEBUG_RETURN( -res );
	}
	if(monitor)mprintf(" res=OK\n");
	return 0;
}
#endif /* HAVE_SETXATTR */

static struct fuse_operations userModeFS_oper = {
	.init = userModeFS_init,
	.access	= userModeFS_access,
	.chmod	= userModeFS_chmod,
	.chown	= userModeFS_chown,
	.flush	= userModeFS_flush,
	.fsync	= userModeFS_fsync,
	.getattr	= userModeFS_getattr,
	.link	= userModeFS_link,
	.mkdir	= userModeFS_mkdir,
	.mknod	= userModeFS_mknod,
	.open	= userModeFS_open,
	.opendir	= userModeFS_opendir,
	.read	= userModeFS_read,
	.readlink	= userModeFS_readlink,
	.readdir	= userModeFS_readdirMethod1,
	.release	= userModeFS_release,
	.releasedir	= userModeFS_releasedir,
	.rename	= userModeFS_rename,
	.rmdir	= userModeFS_rmdir,
	.statfs	= userModeFS_statfs,
	.symlink	= userModeFS_symlink,
	.truncate	= userModeFS_truncate,
	.unlink	= userModeFS_unlink,
	.utime	= userModeFS_utime,
	.write	= userModeFS_write,
#ifdef HAVE_SETXATTR
	.getxattr	= userModeFS_getxattr,
	.listxattr	= userModeFS_listxattr,
	.removexattr	= userModeFS_removexattr,
	.setxattr	= userModeFS_setxattr,
#endif
};
int userFSMain(struct fuse_args *args,int use_readir_method2){
	sigset_t set;

	sigemptyset(&set);
	sigaddset(&set, SIGUSR1);
	sigaddset(&set, SIGUSR2);
	pthread_sigmask(SIG_BLOCK, &set, NULL);

	s_file_table = g_hash_table_new(g_str_hash, g_str_equal);
	s_dir_table = g_hash_table_new(g_str_hash, g_str_equal);

	if ((s_file_table == NULL) || (s_dir_table == NULL)) {
        DEBUG_RETURN( -ENOMEM );
	}

	pthread_mutexattr_t* attrp = NULL;
#ifdef MUTEX_DEBUG
	pthread_mutexattr_t attr;
	attrp = &attr;
	pthread_mutexattr_init( attrp );
	pthread_mutexattr_settype( attrp, PTHREAD_MUTEX_ERRORCHECK );
#endif
	pthread_mutex_init(&s_file_table_mutex, attrp );
	pthread_mutex_init(&s_dir_table_mutex, attrp );

	if(use_readir_method2)userModeFS_oper.readdir	= userModeFS_readdirMethod2;
	return(fuse_main(args->argc, args->argv, &userModeFS_oper, NULL));
}

