/*
 * Copyright Intel Corp. 2020-2021
 *
 * ch_process.h: header file for Cloud-Hypervisor's process controller
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

#include "sfvm_conf.h"
#include "internal.h"

int virCHProcessStart(virCHDriver *driver,
                      virDomainObj *vm,
                      virDomainRunningReason reason);
int virCHProcessStop(virCHDriver *driver,
                     virDomainObj *vm,
                     virDomainShutoffReason reason);

int virCHProcessSetupVcpu(virDomainObj *vm,
                          unsigned int vcpuid);

int virSFVMProcessStart(virCHDriver *driver,
                        virDomainObj *vm,
                        virDomainRunningReason reason);

int virSFVMMonitorProcessDisk(virDomainDef *vmdef, const char* bit_bin_file_in_lib);

int
virSFVMMonitorProcessFPGAFlags(virCaps* caps ATTRIBUTE_UNUSED,
                               int write_flag);


int
virSFVMMonitorProcessFPGAFirmware(virCaps* caps ATTRIBUTE_UNUSED,
                                const char *content);

int
virSFVMMonitorCreateVM(virCHDriver *driver,
                  virDomainObj *vm);
