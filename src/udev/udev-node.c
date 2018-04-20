/* SPDX-License-Identifier: GPL-2.0+ */

#include <errno.h>
#include <fcntl.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#include <sys/sem.h>

#include "alloc-util.h"
#include "device-nodes.h"
#include "device-private.h"
#include "device-util.h"
#include "dirent-util.h"
#include "fd-util.h"
#include "format-util.h"
#include "fs-util.h"
#include "libudev-util.h"
#include "mkdir.h"
#include "path-util.h"
#include "selinux-util.h"
#include "smack-util.h"
#include "stdio-util.h"
#include "string-util.h"
#include "strxcpyx.h"
#include "udev-node.h"
#include "siphash24.h"
#include "hash-funcs.h"
#include "udev.h"

static int node_symlink(sd_device *dev, const char *node, const char *slink) {
        _cleanup_free_ char *slink_dirname = NULL, *target = NULL;
        const char *id_filename, *slink_tmp;
        struct stat stats;
        int r;

        assert(dev);
        assert(node);
        assert(slink);

        slink_dirname = dirname_malloc(slink);
        if (!slink_dirname)
                return log_oom();

        /* use relative link */
        r = path_make_relative(slink_dirname, node, &target);
        if (r < 0)
                return log_device_error_errno(dev, r, "Failed to get relative path from '%s' to '%s': %m", slink, node);

        /* preserve link with correct target, do not replace node of other device */
        if (lstat(slink, &stats) == 0) {
                if (S_ISBLK(stats.st_mode) || S_ISCHR(stats.st_mode)) {
                        log_device_error(dev, "Conflicting device node '%s' found, link to '%s' will not be created.", slink, node);
                        return -EOPNOTSUPP;
                } else if (S_ISLNK(stats.st_mode)) {
                        _cleanup_free_ char *buf = NULL;

                        if (readlink_malloc(slink, &buf) >= 0 &&
                            streq(target, buf)) {
                                log_device_debug(dev, "Preserve already existing symlink '%s' to '%s'", slink, target);
                                (void) label_fix(slink, LABEL_IGNORE_ENOENT);
                                (void) utimensat(AT_FDCWD, slink, NULL, AT_SYMLINK_NOFOLLOW);
                                return 0;
                        }
                }
        } else {
                log_device_debug(dev, "Creating symlink '%s' to '%s'", slink, target);
                do {
                        r = mkdir_parents_label(slink, 0755);
                        if (!IN_SET(r, 0, -ENOENT))
                                break;
                        mac_selinux_create_file_prepare(slink, S_IFLNK);
                        if (symlink(target, slink) < 0)
                                r = -errno;
                        mac_selinux_create_file_clear();
                } while (r == -ENOENT);
                if (r == 0)
                        return 0;
                if (r < 0)
                        log_device_debug_errno(dev, r, "Failed to create symlink '%s' to '%s', trying to replace '%s': %m", slink, target, slink);
        }

        log_device_debug(dev, "Atomically replace '%s'", slink);
        r = device_get_id_filename(dev, &id_filename);
        if (r < 0)
                return log_device_error_errno(dev, r, "Failed to get id_filename: %m");
        slink_tmp = strjoina(slink, ".tmp-", id_filename);
        (void) unlink(slink_tmp);
        do {
                r = mkdir_parents_label(slink_tmp, 0755);
                if (!IN_SET(r, 0, -ENOENT))
                        break;
                mac_selinux_create_file_prepare(slink_tmp, S_IFLNK);
                if (symlink(target, slink_tmp) < 0)
                        r = -errno;
                mac_selinux_create_file_clear();
        } while (r == -ENOENT);
        if (r < 0)
                return log_device_error_errno(dev, r, "Failed to create symlink '%s' to '%s': %m", slink_tmp, target);

        if (rename(slink_tmp, slink) < 0) {
                r = log_device_error_errno(dev, errno, "Failed to rename '%s' to '%s' failed: %m", slink_tmp, slink);
                (void) unlink(slink_tmp);
        }

        return r;
}

static const char links_dirname[] = "/run/udev/links/";
#define PRIONAME_SIZE 32
static const char prio_prefix[] = "L:";

static int make_prio_name(int prio, char *buf, size_t buflen)
{
        return snprintf(buf, buflen, "%s%d", prio_prefix, prio);
}

static bool is_prio_name(const char *name, int *priority)
{
        int len = sizeof(prio_prefix) - 1;
        long prio;
        char *e;

        if (!name || strncmp(name, prio_prefix, len) || name[len] == '\0')
                return false;

        prio = strtol(name + len, &e, 10);
        if (*e != '\0' || prio < INT_MIN || prio >INT_MAX)
                return false;

        *priority = prio;
        return true;
}

static bool is_prio_dirent(DIR *dir, struct dirent *de, int *priority)
{
        int prio;

        if (!is_prio_name(de->d_name, &prio))
                return  false;

        dirent_ensure_type(dir, de);
        if (de->d_type != DT_DIR)
                return false;

        *priority = prio;
        return true;
}

enum {
        NO_TARGET_FOUND,
        TARGET_FOUND,
};

/* find device node of device with highest priority */
static int link_find_prioritized(sd_device *dev, bool add, DIR *dir,
                                 const char *slink, char **ret) {
        _cleanup_free_ char *target = NULL;
        struct dirent *dent;
        int priority;

        assert(!add || dev);
        assert(dir);
        assert(ret);

        if (add) {
                const char *devnode;
                int r;

                r = device_get_devlink_priority(dev, &priority);
                if (r < 0)
                        return r;

                r = sd_device_get_devname(dev, &devnode);
                if (r < 0)
                        return r;

                target = strdup(devnode);
                if (!target)
                        return -ENOMEM;
        } else
                priority = INT_MIN;

        rewinddir(dir);
        FOREACH_DIRENT_ALL(dent, dir, break) {
                int prio = INT_MIN;

                if (dent->d_name[0] == '\0')
                        break;
                if (dot_or_dot_dot(dent->d_name))
                        continue;
                if (!is_prio_dirent(dir, dent, &prio))
                        continue;

                if (prio > priority) {
                        _cleanup_closedir_ DIR *pdir = NULL;
                        _cleanup_(sd_device_unrefp) sd_device *dev_db = NULL;
                        int priofd;
                        const char *devnode;
                        char *tmp;
                        struct dirent *other;

                        priofd = openat(dirfd(dir), dent->d_name, O_RDONLY|O_DIRECTORY);
                        /* May race with another remove */
                        if (priofd == -1)
                                continue;
                        pdir = fdopendir(priofd);
                        if (!pdir) {
                                close(priofd);
                                continue;
                        }

                        /*
                         * All entries in this directory have the same prio.
                         * Thus it's sufficient to read the first one.
                         */
                        other = readdir_no_dot(pdir);
                        if (!other)
                                continue;

                        if (sd_device_new_from_device_id(&dev_db,
                                                         other->d_name) < 0)
                                continue;

                        if (sd_device_get_devname(dev_db, &devnode) < 0)
                                continue;

                        tmp = target;
                        if (free_and_strdup(&target, devnode) < 0) {
                                target = tmp;
                                continue;
                        }

                        log_device_debug(dev_db, "Device claims priority %i for '%s'",
                                         prio, slink);
                        priority = prio;
                }
        }

        if (!target) {
                log_device_debug(dev, "nothing claims %s", slink);
                return NO_TARGET_FOUND;
        }

        *ret = TAKE_PTR(target);
        return TARGET_FOUND;
}

static int create_target_entry(int dirfd, const char *prioname,
                               const char *filename, const char *slink)
{
        _cleanup_close_ int priofd = -1;

        mkdirat(dirfd, prioname, 0755);
        priofd = openat(dirfd, prioname, O_RDONLY|O_DIRECTORY);
        if (priofd == -1)
                return log_error_errno(-errno, "Failed to open %s", prioname);

        if (symlinkat(".", priofd, filename) != 0 && errno != -EEXIST)
                return log_error_errno(-errno,
                                       "Failed to add target %s/%s for %s",
                                       prioname, filename, slink);
        log_debug("added target %s/%s for %s", prioname, filename, slink);
        return 0;
}

static int delete_target_entry(int dirfd, const char *prioname,
                               const char *filename, const char *slink)
{
        _cleanup_close_ int priofd;
        int r;

        priofd = openat(dirfd, prioname, O_RDONLY|O_DIRECTORY);
        if (priofd == -1) {
                if (errno == ENOENT)
                        return 0;
                else
                        return log_error_errno(-errno, "Failed to open %s",
                                               prioname);
        }

        r = unlinkat(priofd, filename, 0);
        if (r != 0 && errno != ENOENT)
                return log_error_errno(-errno,
                                       "Failed to remove target %s/%s for %s",
                                       prioname, filename, slink);
        else if (r == 0)
                log_debug("removed target %s/%s for %s",
                          prioname, filename, slink);

        r = unlinkat(dirfd, prioname, AT_REMOVEDIR);
        if (r != 0 && errno != ENOTEMPTY && errno != ENOENT)
                log_warning_errno(-errno, "failed to remove prio dir %s for %s",
                                  prioname, slink);
        else if (r == 0)
                log_debug("removed prio dir %s for %s", prioname, slink);
        return 0;
}

#define NSEM 1024
static int init_link_semaphores(const char *path)
{
        key_t key = ftok(path, 0);
        int semid;

        semid = semget(key, NSEM, 0600|IPC_CREAT|IPC_EXCL);
        if (semid != -1) {
                unsigned short val[NSEM];
                int i;
                struct sembuf dummy_op[]  = {
                        { .sem_num = 0, .sem_op = -1, .sem_flg = 0 },
                        { .sem_num = 0, .sem_op = 1, .sem_flg = 0 },
                };

                for (i = 0; i < NSEM; i++)
                        val[i] = 1;
                if (semctl(semid, 0, SETALL, val) == -1)
                        return -errno;

                /* Dummy semop to set sem_otime */
                if (semop(semid, dummy_op, (sizeof(dummy_op)/sizeof(*dummy_op)))
                    == -1)
                        return -errno;
                return semid;
        } else {
                const int RETRIES = 10;
                int i;

                semid = semget(key, NSEM, 0);
                if (semid == -1)
                        return -errno;

                for (i = 0; i < RETRIES; i++) {
                        struct semid_ds ds;

                        /* Wait for initialization to finish */
                        if (semctl(semid, 0, IPC_STAT, &ds) != -1 &&
                            ds.sem_otime != 0)
                                return semid;
                        usleep(10000);
                }
                return -1;
        }
}

static unsigned short get_sema_index(const char *link)
{
        static const unsigned char seed[16] = { 0x6b, 0xb0, 0xb1, 0x28,
                                                0xf7, 0x8c, 0x59, 0xb2,
                                                0x05, 0x1d, 0xd1, 0xa2,
                                                0xcc, 0x12, 0xae, 0xb7 };
        struct siphash state;
        uint64_t hash;

        siphash24_init(&state, seed);
        path_hash_func(link, &state);
        hash = siphash24_finalize(&state);

        return hash & (NSEM-1);
}

static int _slink_semop(int semid, unsigned short semidx,
                        int op, const char *msg)
{
        struct sembuf sb = { .sem_num = semidx, .sem_op = op, .sem_flg = 0 };

        if (semop(semid, &sb, 1) == -1)
                return log_warning_errno(-errno, "failed to %s semaphore", msg);
        return 0;
}

#define lock_slink(semid, semidx) \
        _slink_semop((semid), (semidx), -1, "acquire")
#define unlock_slink(semid, semidx) \
        _slink_semop((semid), (semidx), 1, "release")

/* manage "stack of names" with possibly specified device priorities */
static int link_update(sd_device *dev, const char *slink, bool add) {
        _cleanup_free_ char *target = NULL, *dirname = NULL;
        _cleanup_close_ int links_fd;
        _cleanup_closedir_ DIR *dir = NULL;
        char name_enc[PATH_MAX];
        const char *id_filename;
        char prioname[PRIONAME_SIZE];
        int dfd, priority;
        static int semid = -1;
        unsigned short semidx;
        int r;

        assert(dev);
        assert(slink);

        if (semid == -1) {
                semid = init_link_semaphores("/run/udev/links");
                if (semid == -1)
                        return log_device_error_errno(dev, r,
                                                      "failed to set up semaphores: %m");
        }
        mkdir_p(links_dirname, 0755);
        links_fd = open(links_dirname, O_RDONLY|O_DIRECTORY);
        if (links_fd == -1)
                return log_error_errno(-errno, "failed to open %s", dirname);

        r = device_get_id_filename(dev, &id_filename);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get id_filename: %m");

        util_path_encode(slink + STRLEN("/dev"), name_enc, sizeof(name_enc));
        dirname = path_join(links_dirname, name_enc);
        if (!dirname)
                return log_oom();

        r = device_get_devlink_priority(dev, &priority);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get devlink prio: %m");
        make_prio_name(priority, prioname, sizeof(prioname));

        if (add) {
                mkdirat(links_fd, name_enc, 0755);
                dfd = openat(links_fd, name_enc, O_RDONLY|O_DIRECTORY);
                if (dfd == -1)
                        return log_device_error_errno(dev, -errno,
                                                      "failed to open %s",
                                                      dirname);
                create_target_entry(dfd, prioname, id_filename, slink);
        } else {
                dfd = openat(links_fd, name_enc, O_RDONLY|O_DIRECTORY);
                if (dfd == -1 && errno != ENOENT)
                        return log_device_error_errno(dev, -errno,
                                                      "failed to open %s",
                                                      dirname);
                delete_target_entry(dfd, prioname, id_filename, slink);
        }

        dir = fdopendir(dfd);
        if (!dir) {
                close(dfd);
                return log_device_error_errno(dev, -errno,
                                              "fdopendir: %m");
        }

        semidx = get_sema_index(slink);
        r = lock_slink(semid, semidx);
        if (r != 0)
                return r;

        r = link_find_prioritized(dev, add, dir, slink, &target);
        if (r != TARGET_FOUND) {
                log_debug("no reference left, remove '%s'", slink);
                if (unlink(slink) == 0)
                        (void) rmdir_parents(slink, "/");
        } else {
                log_debug("creating link '%s' to '%s'", slink, target);
                mkdir_parents(slink, 0755);
                node_symlink(dev, target, slink);
        }

        (void)unlock_slink(semid, semidx);
        return 0;
}

int udev_node_update_old_links(sd_device *dev, sd_device *dev_old) {
        const char *name, *devpath;
        int r;

        assert(dev);
        assert(dev_old);

        r = sd_device_get_devpath(dev, &devpath);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get devpath: %m");

        /* update possible left-over symlinks */
        FOREACH_DEVICE_DEVLINK(dev_old, name) {
                const char *name_current;
                bool found = false;

                /* check if old link name still belongs to this device */
                FOREACH_DEVICE_DEVLINK(dev, name_current)
                        if (streq(name, name_current)) {
                                found = true;
                                break;
                        }

                if (found)
                        continue;

                log_device_debug(dev, "Updating old name, '%s' no longer belonging to '%s'",
                                 name, devpath);
                link_update(dev, name, false);
        }

        return 0;
}

static int node_permissions_apply(sd_device *dev, bool apply,
                                  mode_t mode, uid_t uid, gid_t gid,
                                  Hashmap *seclabel_list) {
        const char *devnode, *subsystem, *id_filename = NULL;
        struct stat stats;
        dev_t devnum;
        int r = 0;

        assert(dev);

        r = sd_device_get_devname(dev, &devnode);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get devname: %m");
        r = sd_device_get_subsystem(dev, &subsystem);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get subsystem: %m");
        r = sd_device_get_devnum(dev, &devnum);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get devnum: %m");
        (void) device_get_id_filename(dev, &id_filename);

        if (streq(subsystem, "block"))
                mode |= S_IFBLK;
        else
                mode |= S_IFCHR;

        if (lstat(devnode, &stats) < 0)
                return log_device_debug_errno(dev, errno, "cannot stat() node '%s' (%m)", devnode);

        if (((stats.st_mode & S_IFMT) != (mode & S_IFMT)) || (stats.st_rdev != devnum))
                return log_device_debug_errno(dev, EEXIST, "Found node '%s' with non-matching devnum %s, skip handling",
                                              devnode, id_filename);

        if (apply) {
                bool selinux = false, smack = false;
                const char *name, *label;
                Iterator i;

                if ((stats.st_mode & 0777) != (mode & 0777) || stats.st_uid != uid || stats.st_gid != gid) {
                        log_device_debug(dev, "Setting permissions %s, %#o, uid=%u, gid=%u", devnode, mode, uid, gid);
                        if (chmod(devnode, mode) < 0)
                                r = log_device_warning_errno(dev, errno, "Failed to set mode of %s to %#o: %m", devnode, mode);
                        if (chown(devnode, uid, gid) < 0)
                                r = log_device_warning_errno(dev, errno, "Failed to set owner of %s to uid=%u, gid=%u: %m", devnode, uid, gid);
                } else
                        log_device_debug(dev, "Preserve permissions of %s, %#o, uid=%u, gid=%u", devnode, mode, uid, gid);

                /* apply SECLABEL{$module}=$label */
                HASHMAP_FOREACH_KEY(label, name, seclabel_list, i) {
                        int q;

                        if (streq(name, "selinux")) {
                                selinux = true;

                                q = mac_selinux_apply(devnode, label);
                                if (q < 0)
                                        log_device_error_errno(dev, q, "SECLABEL: failed to set SELinux label '%s': %m", label);
                                else
                                        log_device_debug(dev, "SECLABEL: set SELinux label '%s'", label);

                        } else if (streq(name, "smack")) {
                                smack = true;

                                q = mac_smack_apply(devnode, SMACK_ATTR_ACCESS, label);
                                if (q < 0)
                                        log_device_error_errno(dev, q, "SECLABEL: failed to set SMACK label '%s': %m", label);
                                else
                                        log_device_debug(dev, "SECLABEL: set SMACK label '%s'", label);

                        } else
                                log_device_error(dev, "SECLABEL: unknown subsystem, ignoring '%s'='%s'", name, label);
                }

                /* set the defaults */
                if (!selinux)
                        (void) mac_selinux_fix(devnode, LABEL_IGNORE_ENOENT);
                if (!smack)
                        (void) mac_smack_apply(devnode, SMACK_ATTR_ACCESS, NULL);
        }

        /* always update timestamp when we re-use the node, like on media change events */
        (void) utimensat(AT_FDCWD, devnode, NULL, 0);

        return r;
}

static int xsprintf_dev_num_path_from_sd_device(sd_device *dev, char **ret) {
        char filename[DEV_NUM_PATH_MAX], *s;
        const char *subsystem;
        dev_t devnum;
        int r;

        assert(ret);

        r = sd_device_get_subsystem(dev, &subsystem);
        if (r < 0)
                return r;

        r = sd_device_get_devnum(dev, &devnum);
        if (r < 0)
                return r;

        xsprintf_dev_num_path(filename,
                              streq(subsystem, "block") ? "block" : "char",
                              devnum);

        s = strdup(filename);
        if (!s)
                return -ENOMEM;

        *ret = s;
        return 0;
}

int udev_node_add(sd_device *dev, bool apply,
                  mode_t mode, uid_t uid, gid_t gid,
                  Hashmap *seclabel_list) {
        const char *devnode, *devlink;
        _cleanup_free_ char *filename = NULL;
        int r;

        assert(dev);

        r = sd_device_get_devname(dev, &devnode);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get devnode: %m");

        if (DEBUG_LOGGING) {
                const char *id_filename = NULL;

                (void) device_get_id_filename(dev, &id_filename);
                log_device_debug(dev, "Handling device node '%s', devnum=%s, mode=%#o, uid="UID_FMT", gid="GID_FMT,
                                 devnode, strnull(id_filename), mode, uid, gid);
        }

        r = node_permissions_apply(dev, apply, mode, uid, gid, seclabel_list);
        if (r < 0)
                return r;

        r = xsprintf_dev_num_path_from_sd_device(dev, &filename);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get device path: %m");

        /* always add /dev/{block,char}/$major:$minor */
        (void) node_symlink(dev, devnode, filename);

        /* create/update symlinks, add symlinks to name index */
        FOREACH_DEVICE_DEVLINK(dev, devlink)
                (void) link_update(dev, devlink, true);

        return 0;
}

int udev_node_remove(sd_device *dev) {
        _cleanup_free_ char *filename = NULL;
        const char *devlink;
        int r;

        assert(dev);

        /* remove/update symlinks, remove symlinks from name index */
        FOREACH_DEVICE_DEVLINK(dev, devlink)
                (void) link_update(dev, devlink, false);

        r = xsprintf_dev_num_path_from_sd_device(dev, &filename);
        if (r < 0)
                return log_device_debug_errno(dev, r, "Failed to get device path: %m");

        /* remove /dev/{block,char}/$major:$minor */
        (void) unlink(filename);

        return 0;
}
