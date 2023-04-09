/*
 * Copyright Intel Corp. 2020-2021
 *
 * ch_conf.c: functions for Cloud-Hypervisor configuration
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#include <config.h>
#include <fcntl.h>
#include <sys/mman.h>

#include "configmake.h"
#include "vircommand.h"
#include "virlog.h"
#include "virobject.h"
#include "virstring.h"
#include "virutil.h"
#include "virfile.h"
#include "viralloc.h"

#include "sfvm_conf.h"
#include "sfvm_domain.h"

#define VIR_FROM_THIS VIR_FROM_SFVM

VIR_LOG_INIT("sfvm.sfvm_conf");

static virClass *virCHDriverConfigClass;
static void virCHDriverConfigDispose(void *obj);

static int virCHConfigOnceInit(void)
{
    if (!VIR_CLASS_NEW(virCHDriverConfig, virClassForObject()))
        return -1;

    return 0;
}

VIR_ONCE_GLOBAL_INIT(virCHConfig);


/* Functions */
virCaps *virCHDriverCapsInit(void)
{
    g_autoptr(virCaps) caps = NULL;
    virCapsGuest *guest;

    if ((caps = virCapabilitiesNew(virArchFromHost(),
                                   false, false)) == NULL)
        return NULL;

    if (!(caps->host.numa = virCapabilitiesHostNUMANewHost()))
        return NULL;

    if (virCapabilitiesInitCaches(caps) < 0)
        return NULL;

    guest = virCapabilitiesAddGuest(caps, VIR_DOMAIN_OSTYPE_HVM,
                                    caps->host.arch, NULL, NULL, 0, NULL);

    virCapabilitiesAddGuestDomain(guest, VIR_DOMAIN_VIRT_KVM,
                                  NULL, NULL, 0, NULL);
    return g_steal_pointer(&caps);
}

/**
 * virCHDriverGetCapabilities:
 *
 * Get a reference to the virCaps instance for the
 * driver. If @refresh is true, the capabilities will be
 * rebuilt first
 *
 * The caller must release the reference with virObjetUnref
 *
 * Returns: a reference to a virCaps instance or NULL
 */
virCaps *virCHDriverGetCapabilities(virCHDriver *driver,
                                      bool refresh)
{
    virCaps *ret = NULL;
    virCaps *caps = NULL;

    if (refresh && !(caps = virCHDriverCapsInit()))
        return NULL;

    VIR_WITH_MUTEX_LOCK_GUARD(&driver->lock) {
        if (refresh) {
            virObjectUnref(driver->caps);
            driver->caps = caps;
        }

        ret = virObjectRef(driver->caps);
    }

    return ret;
}

virDomainXMLOption *
chDomainXMLConfInit(virCHDriver *driver)
{
    virCHDriverDomainDefParserConfig.priv = driver;
    return virDomainXMLOptionNew(&virCHDriverDomainDefParserConfig,
                                 &virCHDriverPrivateDataCallbacks,
                                 NULL, NULL, NULL, NULL);
}

virCHDriverConfig *
virCHDriverConfigNew(bool privileged)
{
    virCHDriverConfig *cfg;

    if (virCHConfigInitialize() < 0)
        return NULL;

    if (!(cfg = virObjectNew(virCHDriverConfigClass)))
        return NULL;

    cfg->cgroupControllers = -1; /* Auto detect */

    if (privileged) {
        if (virGetUserID(CH_USER, &cfg->user) < 0)
            return NULL;
        if (virGetGroupID(CH_GROUP, &cfg->group) < 0)
            return NULL;
    } else {
        cfg->user = (uid_t)-1;
        cfg->group = (gid_t)-1;
    }

    if (privileged) {
        cfg->logDir = g_strdup_printf("%s/log/libvirt/sfvm", LOCALSTATEDIR);
        cfg->stateDir = g_strdup_printf("%s/libvirt/sfvm", RUNSTATEDIR);

    } else {
        g_autofree char *rundir = NULL;
        g_autofree char *cachedir = NULL;

        cachedir = virGetUserCacheDirectory();

        cfg->logDir = g_strdup_printf("%s/sfvm/log", cachedir);

        rundir = virGetUserRuntimeDirectory();
        cfg->stateDir = g_strdup_printf("%s/sfvm/run", rundir);
    }

    return cfg;
}

virCHDriverConfig *virCHDriverGetConfig(virCHDriver *driver)
{
    VIR_LOCK_GUARD lock = virLockGuardLock(&driver->lock);
    return virObjectRef(driver->config);
}

static void
virCHDriverConfigDispose(void *obj)
{
    virCHDriverConfig *cfg = obj;

    g_free(cfg->stateDir);
    g_free(cfg->logDir);
}

#define MIN_VERSION ((15 * 1000000) + (0 * 1000) + (0))

int
chExtractVersion(virCHDriver *driver)
{
    unsigned long long version;
    g_autofree char *help = NULL;
    char *tmp = NULL;
    g_autofree char *ch_cmd = g_find_program_in_path(CH_CMD);
    g_autoptr(virCommand) cmd = NULL;

    if (!ch_cmd)
        return -2;

    cmd = virCommandNewArgList(ch_cmd, "--version", NULL);
    virCommandAddEnvString(cmd, "LC_ALL=C");
    virCommandSetOutputBuffer(cmd, &help);

    if (virCommandRun(cmd, NULL) < 0)
        return -1;

    tmp = help;

    /* expected format: cloud-hypervisor v<major>.<minor>.<micro> */
    if ((tmp = STRSKIP(tmp, "cloud-hypervisor v")) == NULL) {
        virReportError(VIR_ERR_INTERNAL_ERROR, "%s",
                       _("Unexpected output of cloud-hypervisor binary"));
        return -1;
    }

    if (virStringParseVersion(&version, tmp, true) < 0) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("Unable to parse cloud-hypervisor version: %1$s"), tmp);
        return -1;
    }

    if (version < MIN_VERSION) {
        virReportError(VIR_ERR_INTERNAL_ERROR, "%s",
                       _("Cloud-Hypervisor version is too old (v15.0 is the minimum supported version)"));
        return -1;
    }

    driver->version = version;
    return 0;
}


char *
virCHCapsGetMagicFileContent(virCaps* caps ATTRIBUTE_UNUSED)
{
    FILE *fh = NULL;
    char *content = NULL;
    char *ret = NULL;

    if (VIR_CONNECT_MAGIC_FILE_STATUS_UNREADABLE
          == virCHCapsGetMagicFileStatus(caps)) {
        return NULL;
    }

    if (!(fh = fopen(VIR_CONNECT_MAGIC_FILE_PATH, "r"))) {
        virReportSystemError(errno, _("failed to open file %s"),
                             VIR_CONNECT_MAGIC_FILE_PATH);
        return NULL;
    }
    VIR_REALLOC_N(content, VIR_CONNECT_MAGIC_FILE_CONTENT_LEN);

    memset(content, 0, VIR_CONNECT_MAGIC_FILE_CONTENT_LEN);

    if (!fgets(content, VIR_CONNECT_MAGIC_FILE_CONTENT_LEN, fh)) {
        virReportSystemError(errno, _("failed to read file %s"),
                             VIR_CONNECT_MAGIC_FILE_PATH);
        ret = NULL;
        goto cleanup;
    }

    ret = content;

 cleanup:
    if (VIR_FCLOSE(fh) < 0) {
        virReportSystemError(errno, _("failed to close file %d"), fileno(fh));
    }

    return ret;
}


int
virCHCapsSetMagicFileContent(virCaps* caps ATTRIBUTE_UNUSED,
                               const char *content)
{
    FILE *fh = NULL;
    size_t content_len = 0;
    int ret = -1;

    if (!content) {
        return -1;
    }

    if (!(fh = fopen(VIR_CONNECT_MAGIC_FILE_PATH, "w"))) {
        virReportSystemError(errno, _("failed to open file %s"),
                             VIR_CONNECT_MAGIC_FILE_PATH);
        return -1;
    }

    if ((content_len = strlen(content)) > VIR_CONNECT_MAGIC_FILE_CONTENT_LEN) {
        content_len = VIR_CONNECT_MAGIC_FILE_CONTENT_LEN;
    }

    if (content_len != fwrite(content, sizeof(char), content_len, fh)) {
        ret = -1;
        goto cleanup;
    }

    ret = 1;

 cleanup:
    if (VIR_FCLOSE(fh) < 0) {
        virReportSystemError(errno, _("failed to close file %d"), fileno(fh));
    }

    return ret;
}


int
virCHCapsGetMagicFileStatus(virCaps* caps ATTRIBUTE_UNUSED)
{
    if (-1 == access(VIR_CONNECT_MAGIC_FILE_PATH, R_OK)) {
        return VIR_CONNECT_MAGIC_FILE_STATUS_UNREADABLE;
    }

    return VIR_CONNECt_MAGIC_FILE_STATUS_READABLE;
}

char *virSFVMCapsReadDevMem(virCaps* caps ATTRIBUTE_UNUSED, unsigned long long mem_addr)
{
    int fd = 0;
    void *map_base = NULL, *virt_addr = NULL;
    unsigned page_size = 0, mapped_size = 0, offset_in_page = 0;
    unsigned int ret_val = 0;
    char *ret_str = NULL;
    int ret_str_buf_len = 32;

    if (!(fd = open("/dev/mem", (O_RDWR|O_SYNC)))) {
        VIR_ERROR(_("Failed to open /dev/mem"));
        return NULL;
    }
    mapped_size = page_size = getpagesize();
    offset_in_page = (unsigned)mem_addr & (page_size - 1);
    if (offset_in_page + 32 > page_size) {
        /* This access spans pages.
         * Must map two pages to make it possible: */
        mapped_size *= 2;
    }
    map_base = mmap(NULL,
               mapped_size,
               (PROT_READ | PROT_WRITE),
               MAP_SHARED,
               fd,
               mem_addr & ~(off_t)(page_size - 1));
    if (!map_base) {
        virReportSystemError(errno, _("failed to mmap /dev/mem %d"),
                             fd);
        goto cleanup;
    }

    virt_addr = (char*)map_base + offset_in_page;
    ret_val = *(volatile unsigned int *)virt_addr;
    VIR_REALLOC_N(ret_str, ret_str_buf_len);
    memset(ret_str, 0, ret_str_buf_len);
    g_snprintf(ret_str, ret_val, "0x%X", ret_str_buf_len);
    VIR_DEBUG("read phy memory 0x%llx, mapped addr %p , content 0x%x, ret_str %s", mem_addr, virt_addr, ret_val, ret_str);

 cleanup:
    if (VIR_CLOSE(fd) < 0) {
        virReportSystemError(errno, _("failed to close file %d"), fd);
    }

    return ret_str;
}

int
virSFVMCapsWriteDevMem(virCaps* caps ATTRIBUTE_UNUSED,
                        unsigned long long mem_addr,
                        u_int32_t write_val)
{
    int fd = 0;
    void *map_base = NULL, *virt_addr = NULL;
    unsigned page_size = 0, mapped_size = 0, offset_in_page = 0;
    int ret = 0;

    if (!(fd = open("/dev/mem", (O_RDWR|O_SYNC)))) {
        VIR_ERROR(_("failed to open /dev/mem"));
        return VIR_CONNECT_RW_DEVMEM_STATUS_FAILED;
    }
    mapped_size = page_size = getpagesize();
    offset_in_page = (unsigned)mem_addr & (page_size - 1);
    if (offset_in_page + 32 > page_size) {
        /* This access spans pages.
         * Must map two pages to make it possible: */
        mapped_size *= 2;
    }
    map_base = mmap(NULL,
            mapped_size,
            (PROT_READ | PROT_WRITE),
            MAP_SHARED,
            fd,
            mem_addr & ~(off_t)(page_size - 1));
    if (!map_base) {
        virReportSystemError(errno, _("failed to mmap /dev/mem %d"),
                             fd);
        ret = VIR_CONNECT_RW_DEVMEM_STATUS_FAILED;
        goto cleanup;
    }

    virt_addr = (char*)map_base + offset_in_page;
    *(volatile u_int32_t*)virt_addr = write_val;
    ret = VIR_CONNECT_RW_DEVMEM_STATUS_SUCESS;

 cleanup:
    if (VIR_CLOSE(fd) < 0) {
        virReportSystemError(errno, _("failed to close file %d"), fd);
    }

    return ret;

}
