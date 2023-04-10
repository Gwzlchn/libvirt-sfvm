/*
 * Copyright Intel Corp. 2020-2021
 *
 * ch_conf.h: header file for Cloud-Hypervisor configuration
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

#pragma once

#include "virdomainobjlist.h"
#include "virthread.h"

#define CH_DRIVER_NAME "CH"
#define CH_CMD "cloud-hypervisor"

#define FPGA_REGION_SYSFS "/sys/class/fpga_region"
#define FPGA_MANAGER_SYSFS "/sys/class/fpga_manager"
#define FPGA_MANAGER_FLAG "/sys/class/fpga_manager/fpga0/flags"
#define FPGA_MANAGER_FIRMWARE "/sys/class/fpga_manager/fpga0/firmware"
#define FPGA_BRIDGE_SYSFS "/sys/class/fpga_bridge"
#define FPGA_BITSTREAM_LIB "/lib/firmware"

#define FPGA_BRIDGE_0_REGBASE 0xb1010000


typedef struct _virCHDriver virCHDriver;

typedef struct _virCHDriverConfig virCHDriverConfig;

struct _virCHDriverConfig {
    GObject parent;

    char *stateDir;
    char *logDir;

    int cgroupControllers;

    uid_t user;
    gid_t group;
};

G_DEFINE_AUTOPTR_CLEANUP_FUNC(virCHDriverConfig, virObjectUnref);

struct _virCHDriver
{
    virMutex lock;

    bool privileged;

    /* Require lock to get a reference on the object,
     * lockless access thereafter */
    virCaps *caps;

    /* Immutable pointer, Immutable object */
    virDomainXMLOption *xmlopt;

    /* Immutable pointer, self-locking APIs */
    virDomainObjList *domains;

    /* Cloud-Hypervisor version */
    int version;

    /* Require lock to get reference on 'config',
     * then lockless thereafter */
    virCHDriverConfig *config;

    /* pid file FD, ensures two copies of the driver can't use the same root */
    int lockFD;

    // the role count in FPGA shell
    int role_cnt;

};

virCaps *virCHDriverCapsInit(void);
virCaps *virCHDriverGetCapabilities(virCHDriver *driver,
                                      bool refresh);
virDomainXMLOption *chDomainXMLConfInit(virCHDriver *driver);
virCHDriverConfig *virCHDriverConfigNew(bool privileged);
virCHDriverConfig *virCHDriverGetConfig(virCHDriver *driver);
int chExtractVersion(virCHDriver *driver);

char *virCHCapsGetMagicFileContent(virCaps* caps);

int virCHCapsSetMagicFileContent(virCaps* caps, const char *content);

int virCHCapsGetMagicFileStatus(virCaps* caps);

char *virSFVMCapsReadDevMem(virCaps* caps, unsigned long long mem_addr);

int virSFVMCapsWriteDevMem(virCaps* caps, unsigned long long mem_addr, u_int32_t write_val);

int sfvmExtractFPGARoleCnt(virCHDriver *driver);
