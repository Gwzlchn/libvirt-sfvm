/*
 * sfvm_driver.c: A FPGA hypervisor for use by
 *
 * Copyright (C) 2006-2019 Red Hat, Inc.
 * Copyright (C) 2006 Daniel P. Berrange
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

#include <sys/time.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <libxml/xmlsave.h>


#include "virerror.h"
#include "datatypes.h"
#include "sfvm_driver.h"
#include "viruuid.h"
#include "capabilities.h"
#include "configmake.h"
#include "viralloc.h"
#include "virnetworkobj.h"
#include "interface_conf.h"
#include "checkpoint_conf.h"
#include "domain_conf.h"
#include "domain_driver.h"
#include "domain_event.h"
#include "network_event.h"
#include "snapshot_conf.h"
#include "virfdstream.h"
#include "storage_conf.h"
#include "virstorageobj.h"
#include "storage_event.h"
#include "node_device_conf.h"
#include "virnodedeviceobj.h"
#include "node_device_event.h"
#include "virxml.h"
#include "virthread.h"
#include "virlog.h"
#include "virfile.h"
#include "virtypedparam.h"
#include "virstring.h"
#include "cpu/cpu.h"
#include "virauth.h"
#include "virdomainobjlist.h"
#include "virinterfaceobj.h"
#include "virhostcpu.h"
#include "virdomaincheckpointobjlist.h"
#include "virdomainsnapshotobjlist.h"
#include "virkeycode.h"
#include "virutil.h"

#define VIR_FROM_THIS VIR_FROM_SFVM

VIR_LOG_INIT("sfvm.sfvm_driver");


#define MAX_CPUS 128

struct _sfvmCell {
    unsigned long mem;
    unsigned long freeMem;
    int numCpus;
    virCapsHostNUMACellCPU cpus[MAX_CPUS];
};
typedef struct _sfvmCell sfvmCell;

struct _sfvmAuth {
    char *username;
    char *password;
};
typedef struct _sfvmAuth sfvmAuth;

struct _sfvmDriver {
    virObjectLockable parent;

    virNodeInfo nodeInfo;
    virInterfaceObjList *ifaces;
    bool transaction_running;
    virInterfaceObjList *backupIfaces;
    virStoragePoolObjList *pools;
    virNodeDeviceObjList *devs;
    int numCells;
    sfvmCell *cells;
    size_t numAuths;
    struct _sfvmAuth *auths;

    /* g_atomic access only */
    volatile int nextDomID;

    /* immutable pointer, immutable object after being initialized with
     * sfvmBuildCapabilities */
    virCaps *caps;

    /* immutable pointer, immutable object */
    virDomainXMLOption *xmlopt;

    /* immutable pointer, self-locking APIs */
    virDomainObjList *domains;
    virNetworkObjList *networks;
    virObjectEventState *eventState;
};
typedef struct _sfvmDriver sfvmDriver;

static sfvmDriver *defaultPrivconn;
static virMutex defaultLock = VIR_MUTEX_INITIALIZER;

static virClass *sfvmDriverClass;
static __thread bool sfvmDriverDisposed;
static void sfvmDriverDispose(void *obj);
static int sfvmDriverOnceInit(void)
{
    if (!(VIR_CLASS_NEW(sfvmDriver, virClassForObjectLockable())))
        return -1;

    return 0;
}
VIR_ONCE_GLOBAL_INIT(sfvmDriver);

#define TEST_MODEL "i686"
#define TEST_EMULATOR "/usr/bin/sfvm-hv"

static const virNodeInfo defaultNodeInfo = {
    TEST_MODEL,
    1024*1024*3, /* 3 GB */
    16,
    1400,
    2,
    2,
    2,
    2,
};

static void
sfvmDriverDispose(void *obj)
{
    sfvmDriver *driver = obj;
    size_t i;

    virObjectUnref(driver->caps);
    virObjectUnref(driver->xmlopt);
    virObjectUnref(driver->domains);
    virNodeDeviceObjListFree(driver->devs);
    virObjectUnref(driver->networks);
    virObjectUnref(driver->ifaces);
    virObjectUnref(driver->pools);
    virObjectUnref(driver->eventState);
    for (i = 0; i < driver->numAuths; i++) {
        g_free(driver->auths[i].username);
        g_free(driver->auths[i].password);
    }
    g_free(driver->cells);
    g_free(driver->auths);

    sfvmDriverDisposed = true;
}

typedef struct _sfvmDomainNamespaceDef sfvmDomainNamespaceDef;
struct _sfvmDomainNamespaceDef {
    int runstate;
    bool transient;
    bool hasManagedSave;

    unsigned int num_snap_nodes;
    xmlNodePtr *snap_nodes;
};

typedef struct _sfvmIOThreadInfo sfvmIOThreadInfo;
struct _sfvmIOThreadInfo {
    unsigned int iothread_id;
    unsigned long long poll_max_ns;
    unsigned int poll_grow;
    unsigned int poll_shrink;
};

static void
sfvmDomainDefNamespaceFree(void *data)
{
    sfvmDomainNamespaceDef *nsdata = data;
    size_t i;

    if (!nsdata)
        return;

    for (i = 0; i < nsdata->num_snap_nodes; i++)
        xmlFreeNode(nsdata->snap_nodes[i]);

    g_free(nsdata->snap_nodes);
    g_free(nsdata);
}

static int
sfvmDomainDefNamespaceParse(xmlXPathContextPtr ctxt,
                            void **data)
{
    sfvmDomainNamespaceDef *nsdata = NULL;
    int tmp, n;
    size_t i;
    unsigned int tmpuint;
    g_autofree xmlNodePtr *nodes = NULL;

    nsdata = g_new0(sfvmDomainNamespaceDef, 1);

    n = virXPathNodeSet("./sfvm:domainsnapshot", ctxt, &nodes);
    if (n < 0)
        goto error;

    if (n)
        nsdata->snap_nodes = g_new0(xmlNodePtr, n);

    for (i = 0; i < n; i++) {
        xmlNodePtr newnode = xmlCopyNode(nodes[i], 1);
        if (!newnode) {
            virReportError(VIR_ERR_INTERNAL_ERROR, "%s",
                           _("Failed to copy XML node"));
            goto error;
        }

        nsdata->snap_nodes[nsdata->num_snap_nodes] = newnode;
        nsdata->num_snap_nodes++;
    }

    tmp = virXPathBoolean("boolean(./sfvm:transient)", ctxt);
    if (tmp == -1) {
        virReportError(VIR_ERR_XML_ERROR, "%s", _("invalid transient"));
        goto error;
    }
    nsdata->transient = tmp;

    tmp = virXPathBoolean("boolean(./sfvm:hasmanagedsave)", ctxt);
    if (tmp == -1) {
        virReportError(VIR_ERR_XML_ERROR, "%s", _("invalid hasmanagedsave"));
        goto error;
    }
    nsdata->hasManagedSave = tmp;

    tmp = virXPathUInt("string(./sfvm:runstate)", ctxt, &tmpuint);
    if (tmp == 0) {
        if (tmpuint >= VIR_DOMAIN_LAST) {
            virReportError(VIR_ERR_XML_ERROR,
                           _("runstate '%d' out of range'"), tmpuint);
            goto error;
        }
        nsdata->runstate = tmpuint;
    } else if (tmp == -1) {
        nsdata->runstate = VIR_DOMAIN_RUNNING;
    } else if (tmp == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid runstate"));
        goto error;
    }

    if (nsdata->transient && nsdata->runstate == VIR_DOMAIN_SHUTOFF) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
            _("transient domain cannot have runstate 'shutoff'"));
        goto error;
    }
    if (nsdata->hasManagedSave && nsdata->runstate != VIR_DOMAIN_SHUTOFF) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
            _("domain with managedsave data can only have runstate 'shutoff'"));
        goto error;
    }

    *data = nsdata;
    return 0;

 error:
    sfvmDomainDefNamespaceFree(nsdata);
    return -1;
}

static virCaps *
sfvmBuildCapabilities(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    g_autoptr(virCaps) caps = NULL;
    virCapsGuest *guest;
    int guest_types[] = { VIR_DOMAIN_OSTYPE_HVM,
                          VIR_DOMAIN_OSTYPE_XEN };
    size_t i, j;

    if ((caps = virCapabilitiesNew(VIR_ARCH_I686, false, false)) == NULL)
        return NULL;

    if (virCapabilitiesAddHostFeature(caps, "pae") < 0)
        return NULL;
    if (virCapabilitiesAddHostFeature(caps, "nonpae") < 0)
        return NULL;

    virCapabilitiesHostInitIOMMU(caps);

    caps->host.pagesSize = g_new0(unsigned int, 4);

    caps->host.pagesSize[caps->host.nPagesSize++] = 4;
    caps->host.pagesSize[caps->host.nPagesSize++] = 8;
    caps->host.pagesSize[caps->host.nPagesSize++] = 2048;
    caps->host.pagesSize[caps->host.nPagesSize++] = 1024 * 1024;

    caps->host.numa = virCapabilitiesHostNUMANew();
    for (i = 0; i < privconn->numCells; i++) {
        virCapsHostNUMACellCPU *cpu_cells;
        virCapsHostNUMACellPageInfo *pages;
        size_t nPages = caps->host.nPagesSize - 1;

        cpu_cells = g_new0(virCapsHostNUMACellCPU, privconn->cells[i].numCpus);
        pages = g_new0(virCapsHostNUMACellPageInfo, nPages);

        memcpy(cpu_cells, privconn->cells[i].cpus,
               sizeof(*cpu_cells) * privconn->cells[i].numCpus);

        if (i == 1)
            pages[0].size = caps->host.pagesSize[1];
        else
            pages[0].size = caps->host.pagesSize[0];

        for (j = 1; j < nPages; j++)
            pages[j].size = caps->host.pagesSize[j + 1];

        pages[0].avail = privconn->cells[i].mem / pages[0].size;

        virCapabilitiesHostNUMAAddCell(caps->host.numa,
                                       i, privconn->cells[i].mem,
                                       privconn->cells[i].numCpus, &cpu_cells,
                                       0, NULL,
                                       nPages, &pages,
                                       NULL);
    }

    for (i = 0; i < G_N_ELEMENTS(guest_types); i++) {
        guest = virCapabilitiesAddGuest(caps, guest_types[i], VIR_ARCH_I686,
                                        TEST_EMULATOR, NULL, 0, NULL);

        virCapabilitiesAddGuestDomain(guest, VIR_DOMAIN_VIRT_SFVM,
                                      NULL, NULL, 0, NULL);

        virCapabilitiesAddGuestFeature(guest, VIR_CAPS_GUEST_FEATURE_TYPE_PAE);
        virCapabilitiesAddGuestFeature(guest, VIR_CAPS_GUEST_FEATURE_TYPE_NONPAE);
    }

    caps->host.nsecModels = 1;
    caps->host.secModels = g_new0(virCapsHostSecModel, caps->host.nsecModels);
    caps->host.secModels[0].model = g_strdup("sfvmSecurity");

    caps->host.secModels[0].doi = g_strdup("");

    return g_steal_pointer(&caps);
}


typedef struct _sfvmDomainObjPrivate sfvmDomainObjPrivate;
struct _sfvmDomainObjPrivate {
    sfvmDriver *driver;

    bool frozen[2]; /* used by file system related calls */

    /* used by get/set time APIs */
    long long seconds;
    unsigned int nseconds;

    /* used by IOThread APIs */
    GArray *iothreads;
};


static void *
sfvmDomainObjPrivateAlloc(void *opaque)
{
    sfvmDomainObjPrivate *priv;

    priv = g_new0(sfvmDomainObjPrivate, 1);

    priv->driver = opaque;
    priv->frozen[0] = priv->frozen[1] = false;

    priv->seconds = 627319920;
    priv->nseconds = 0;

    priv->iothreads = g_array_new(FALSE, FALSE, sizeof(sfvmIOThreadInfo));

    return priv;
}


static int
sfvmDomainDevicesDefPostParse(virDomainDeviceDef *dev G_GNUC_UNUSED,
                              const virDomainDef *def G_GNUC_UNUSED,
                              unsigned int parseFlags G_GNUC_UNUSED,
                              void *opaque G_GNUC_UNUSED,
                              void *parseOpaque G_GNUC_UNUSED)
{
    if (dev->type == VIR_DOMAIN_DEVICE_VIDEO &&
        dev->data.video->type == VIR_DOMAIN_VIDEO_TYPE_DEFAULT) {
        if (def->os.type == VIR_DOMAIN_OSTYPE_XEN ||
            def->os.type == VIR_DOMAIN_OSTYPE_LINUX)
            dev->data.video->type = VIR_DOMAIN_VIDEO_TYPE_XEN;
        else if (ARCH_IS_PPC64(def->os.arch))
            dev->data.video->type = VIR_DOMAIN_VIDEO_TYPE_VGA;
        else
            dev->data.video->type = VIR_DOMAIN_VIDEO_TYPE_CIRRUS;
    }

    return 0;
}


static void
sfvmDomainObjPrivateFree(void *data)
{
    sfvmDomainObjPrivate *priv = data;

    g_array_free(priv->iothreads, TRUE);
    g_free(priv);
}


static sfvmDriver *
sfvmDriverNew(void)
{
    virXMLNamespace ns = {
        .parse = sfvmDomainDefNamespaceParse,
        .free = sfvmDomainDefNamespaceFree,
        .prefix = "sfvm",
        .uri = "http://libvirt.org/schemas/domain/sfvm/1.0",
    };
    virDomainDefParserConfig config = {
        .features = VIR_DOMAIN_DEF_FEATURE_MEMORY_HOTPLUG |
                    VIR_DOMAIN_DEF_FEATURE_OFFLINE_VCPUPIN |
                    VIR_DOMAIN_DEF_FEATURE_INDIVIDUAL_VCPUS |
                    VIR_DOMAIN_DEF_FEATURE_USER_ALIAS |
                    VIR_DOMAIN_DEF_FEATURE_FW_AUTOSELECT |
                    VIR_DOMAIN_DEF_FEATURE_NET_MODEL_STRING,
        .devicesPostParseCallback = sfvmDomainDevicesDefPostParse,
        .defArch = VIR_ARCH_I686,
    };
    virDomainXMLPrivateDataCallbacks privatecb = {
        .alloc = sfvmDomainObjPrivateAlloc,
        .free = sfvmDomainObjPrivateFree,
    };
    sfvmDriver *ret;

    if (sfvmDriverInitialize() < 0)
        return NULL;

    if (!(ret = virObjectLockableNew(sfvmDriverClass)))
        return NULL;

    if (!(ret->xmlopt = virDomainXMLOptionNew(&config, &privatecb, &ns, NULL, NULL, NULL)) ||
        !(ret->eventState = virObjectEventStateNew()) ||
        !(ret->ifaces = virInterfaceObjListNew()) ||
        !(ret->domains = virDomainObjListNew()) ||
        !(ret->networks = virNetworkObjListNew()) ||
        !(ret->devs = virNodeDeviceObjListNew()) ||
        !(ret->pools = virStoragePoolObjListNew()))
        goto error;

    g_atomic_int_set(&ret->nextDomID, 1);

    return ret;

 error:
    virObjectUnref(ret);
    return NULL;
}


static const char *defaultConnXML =
"<node>"
"<domain type='sfvm'>"
"  <name>sfvm</name>"
"  <uuid>6695eb01-f6a4-8304-79aa-97f2502e193f</uuid>"
"  <memory>8388608</memory>"
"  <currentMemory>2097152</currentMemory>"
"  <vcpu>2</vcpu>"
"  <os>"
"    <type>hvm</type>"
"  </os>"
"  <devices>"
"    <disk type='file' device='disk'>"
"      <source file='/guest/diskimage1'/>"
"      <target dev='vda' bus='virtio'/>"
"      <address type='pci' domain='0x0000' bus='0x01' slot='0x00' function='0x0'/>"
"    </disk>"
"    <interface type='network'>"
"      <mac address='aa:bb:cc:dd:ee:ff'/>"
"      <source network='default' bridge='virbr0'/>"
"      <address type='pci' domain='0x0000' bus='0x00' slot='0x1' function='0x0'/>"
"    </interface>"
"    <memballoon model='virtio'>"
"      <address type='pci' domain='0x0000' bus='0x00' slot='0x2' function='0x0'/>"
"    </memballoon>"
"  </devices>"
"</domain>"
""
"<network>"
"  <name>default</name>"
"  <uuid>dd8fe884-6c02-601e-7551-cca97df1c5df</uuid>"
"  <bridge name='virbr0'/>"
"  <forward/>"
"  <ip address='192.168.122.1' netmask='255.255.255.0'>"
"    <dhcp>"
"      <range start='192.168.122.2' end='192.168.122.254'/>"
"    </dhcp>"
"  </ip>"
"</network>"
""
"<interface type=\"ethernet\" name=\"eth1\">"
"  <start mode=\"onboot\"/>"
"  <mac address=\"aa:bb:cc:dd:ee:ff\"/>"
"  <mtu size=\"1492\"/>"
"  <protocol family=\"ipv4\">"
"    <ip address=\"192.168.0.5\" prefix=\"24\"/>"
"    <route gateway=\"192.168.0.1\"/>"
"  </protocol>"
"</interface>"
""
"<pool type='dir'>"
"  <name>default-pool</name>"
"  <uuid>dfe224cb-28fb-8dd0-c4b2-64eb3f0f4566</uuid>"
"  <target>"
"    <path>/default-pool</path>"
"  </target>"
"</pool>"
""
"<device>"
"  <name>computer</name>"
"  <capability type='system'>"
"    <hardware>"
"      <vendor>Libvirt</vendor>"
"      <version>Test driver</version>"
"      <serial>123456</serial>"
"      <uuid>11111111-2222-3333-4444-555555555555</uuid>"
"    </hardware>"
"    <firmware>"
"      <vendor>Libvirt</vendor>"
"      <version>Test Driver</version>"
"      <release_date>01/22/2007</release_date>"
"    </firmware>"
"  </capability>"
"</device>"
"<device>"
"  <name>scsi_host1</name>"
"  <parent>computer</parent>"
"  <capability type='scsi_host'>"
"    <host>1</host>"
"    <unique_id>0</unique_id>"
"    <capability type='fc_host'>"
"      <wwnn>2000000012341234</wwnn>"
"      <wwpn>1000000012341234</wwpn>"
"      <fabric_wwn>2000000043214321</fabric_wwn>"
"    </capability>"
"    <capability type='vport_ops'>"
"      <max_vports>127</max_vports>"
"      <vports>1</vports>"
"    </capability>"
"  </capability>"
"</device>"
"<device>"
"  <name>scsi_host2</name>"
"  <parent>computer</parent>"
"  <capability type='scsi_host'>"
"    <host>2</host>"
"    <unique_id>1</unique_id>"
"    <capability type='fc_host'>"
"      <wwnn>2000000056785678</wwnn>"
"      <wwpn>1000000056785678</wwpn>"
"      <fabric_wwn>2000000087658765</fabric_wwn>"
"    </capability>"
"    <capability type='vport_ops'>"
"      <max_vports>127</max_vports>"
"      <vports>0</vports>"
"    </capability>"
"  </capability>"
"</device>"
"<device>"
"  <name>scsi_host11</name>"
"  <parent>scsi_host1</parent>"
"  <capability type='scsi_host'>"
"    <host>11</host>"
"    <unique_id>10</unique_id>"
"    <capability type='fc_host'>"
"      <wwnn>2000000034563456</wwnn>"
"      <wwpn>1000000034563456</wwpn>"
"      <fabric_wwn>2000000043214321</fabric_wwn>"
"    </capability>"
"  </capability>"
 "</device>"
"</node>";


static const char *defaultPoolSourcesLogicalXML =
"<sources>\n"
"  <source>\n"
"    <device path='/dev/sda20'/>\n"
"    <name>sfvmvg1</name>\n"
"    <format type='lvm2'/>\n"
"  </source>\n"
"  <source>\n"
"    <device path='/dev/sda21'/>\n"
"    <name>sfvmvg2</name>\n"
"    <format type='lvm2'/>\n"
"  </source>\n"
"</sources>\n";

static const char *defaultPoolSourcesNetFSXML =
"<sources>\n"
"  <source>\n"
"    <host name='%s'/>\n"
"    <dir path='/sfvmshare'/>\n"
"    <format type='nfs'/>\n"
"  </source>\n"
"</sources>\n";

static const unsigned long long defaultPoolCap = (100 * 1024 * 1024 * 1024ull);
static const unsigned long long defaultPoolAlloc;

static int sfvmStoragePoolObjSetDefaults(virStoragePoolObj *obj);
static int sfvmNodeGetInfo(virConnectPtr conn, virNodeInfoPtr info);
static virNetworkObj *sfvmNetworkObjFindByName(sfvmDriver *privconn, const char *name);

static virDomainObj *
sfvmDomObjFromDomain(virDomainPtr domain)
{
    virDomainObj *vm;
    sfvmDriver *driver = domain->conn->privateData;
    char uuidstr[VIR_UUID_STRING_BUFLEN];

    vm = virDomainObjListFindByUUID(driver->domains, domain->uuid);
    if (!vm) {
        virUUIDFormat(domain->uuid, uuidstr);
        virReportError(VIR_ERR_NO_DOMAIN,
                       _("no domain with matching uuid '%s' (%s)"),
                       uuidstr, domain->name);
    }

    return vm;
}

static char *
sfvmDomainGenerateIfname(virDomainDef *domdef)
{
    int maxif = 1024;
    int ifctr;

    for (ifctr = 0; ifctr < maxif; ++ifctr) {
        virDomainNetDef *net = NULL;
        char *ifname;

        ifname = g_strdup_printf("sfvmnet%d", ifctr);

        /* Generate network interface names */
        if (!(net = virDomainNetFindByName(domdef, ifname)))
            return ifname;
        VIR_FREE(ifname);
    }

    virReportError(VIR_ERR_INTERNAL_ERROR,
                   _("Exceeded max iface limit %d"), maxif);
    return NULL;
}

static int
sfvmDomainGenerateIfnames(virDomainDef *domdef)
{
    size_t i = 0;

    for (i = 0; i < domdef->nnets; i++) {
        char *ifname;
        if (domdef->nets[i]->ifname)
            continue;

        ifname = sfvmDomainGenerateIfname(domdef);
        if (!ifname)
            return -1;

        domdef->nets[i]->ifname = ifname;
    }

    return 0;
}

static void
sfvmDomainGenerateIOThreadInfos(virDomainObj *obj)
{
    size_t i;
    sfvmDomainObjPrivate *priv;

    if (!obj->def->iothreadids || !obj->def->niothreadids)
        return;

    priv = obj->privateData;

    for (i = 0; i < obj->def->niothreadids; i++) {
        sfvmIOThreadInfo iothread;
        iothread.iothread_id = obj->def->iothreadids[i]->iothread_id;
        iothread.poll_max_ns = 32768;
        iothread.poll_grow = 0;
        iothread.poll_shrink = 0;
        g_array_append_val(priv->iothreads, iothread);
    }
}

static void
sfvmDomainShutdownState(virDomainPtr domain,
                        virDomainObj *privdom,
                        virDomainShutoffReason reason)
{
    virDomainObjRemoveTransientDef(privdom);
    virDomainObjSetState(privdom, VIR_DOMAIN_SHUTOFF, reason);

    if (domain)
        domain->id = -1;
}

/* Set up domain runtime state */
static int
sfvmDomainStartState(sfvmDriver *privconn,
                     virDomainObj *dom,
                     virDomainRunningReason reason)
{
    int ret = -1;

    virDomainObjSetState(dom, VIR_DOMAIN_RUNNING, reason);
    dom->def->id = g_atomic_int_add(&privconn->nextDomID, 1);

    if (virDomainObjSetDefTransient(privconn->xmlopt,
                                    dom, NULL) < 0) {
        goto cleanup;
    }

    dom->hasManagedSave = false;
    ret = 0;
 cleanup:
    if (ret < 0)
        sfvmDomainShutdownState(NULL, dom, VIR_DOMAIN_SHUTOFF_FAILED);
    return ret;
}


static char *sfvmBuildFilename(const char *relativeTo,
                               const char *filename)
{
    g_autofree char *basename = NULL;

    if (g_path_is_absolute(filename))
        return g_strdup(filename);

    basename = g_path_get_dirname(relativeTo);

    return g_strdup_printf("%s/%s", basename, filename);
}

static void
sfvmDomainObjCheckCPUTaint(virDomainObj *obj)
{
    switch (obj->def->cpu->mode) {
    case VIR_CPU_MODE_CUSTOM:
        if (obj->def->cpu->model)
            if (STREQ(obj->def->cpu->model, "Deprecated-Test")) {
                virDomainObjTaint(obj, VIR_DOMAIN_TAINT_DEPRECATED_CONFIG);
                virDomainObjDeprecation(obj, "CPU model Deprecated-Test");
            }

        break;
    default:
        break;
    }
}

static void
sfvmDomainObjCheckDiskTaint(virDomainObj *obj,
                            virDomainDiskDef *disk)
{
    if (disk->rawio == VIR_TRISTATE_BOOL_YES)
        virDomainObjTaint(obj, VIR_DOMAIN_TAINT_HIGH_PRIVILEGES);

    if (disk->device == VIR_DOMAIN_DISK_DEVICE_CDROM &&
        virStorageSourceGetActualType(disk->src) == VIR_STORAGE_TYPE_BLOCK &&
        disk->src->path)
        virDomainObjTaint(obj, VIR_DOMAIN_TAINT_CDROM_PASSTHROUGH);
}

static void
sfvmDomainObjCheckHostdevTaint(virDomainObj *obj,
                               virDomainHostdevDef *hostdev)
{
    if (!virHostdevIsSCSIDevice(hostdev))
        return;

    if (hostdev->source.subsys.u.scsi.rawio == VIR_TRISTATE_BOOL_YES)
        virDomainObjTaint(obj, VIR_DOMAIN_TAINT_HIGH_PRIVILEGES);
}

static void
sfvmDomainObjCheckNetTaint(virDomainObj *obj,
                           virDomainNetDef *net)
{
    /* script is only useful for NET_TYPE_ETHERNET (qemu) and
     * NET_TYPE_BRIDGE (xen), but could be (incorrectly) specified for
     * any interface type. In any case, it's adding user sauce into
     * the soup, so it should taint the domain.
     */
    if (net->script != NULL)
        virDomainObjTaint(obj, VIR_DOMAIN_TAINT_SHELL_SCRIPTS);
}

static void
sfvmDomainObjCheckTaint(virDomainObj *obj)
{
    size_t i;

    for (i = 0; i < obj->def->ndisks; i++)
        sfvmDomainObjCheckDiskTaint(obj, obj->def->disks[i]);

    for (i = 0; i < obj->def->nhostdevs; i++)
        sfvmDomainObjCheckHostdevTaint(obj, obj->def->hostdevs[i]);

    for (i = 0; i < obj->def->nnets; i++)
        sfvmDomainObjCheckNetTaint(obj, obj->def->nets[i]);

    if (obj->def->cpu)
        sfvmDomainObjCheckCPUTaint(obj);

    if (obj->def->os.dtb)
        virDomainObjTaint(obj, VIR_DOMAIN_TAINT_CUSTOM_DTB);
}

static xmlNodePtr
sfvmParseXMLDocFromFile(xmlNodePtr node,
                        const char *file)
{
    g_autoptr(xmlDoc) doc = NULL;
    g_autofree char *relFile = NULL;

    if ((relFile = virXMLPropString(node, "file"))) {
        g_autofree char *absFile = sfvmBuildFilename(file, relFile);
        xmlNodePtr newnode = NULL;

        if (!(doc = virXMLParse(absFile, NULL, NULL, (const char *) node->name,
                                NULL, NULL, false)))
            return NULL;

        if (!(newnode = xmlCopyNode(xmlDocGetRootElement(doc), 1))) {
            virReportError(VIR_ERR_INTERNAL_ERROR, "%s",
                           _("Failed to copy XML node"));
            return NULL;
        }

        /* place 'newnode' in place of 'node' in the original XML document object */
        xmlReplaceNode(node, newnode);
        /* free the original node */
        xmlFreeNode(node);
        return newnode;
    }

    return node;
}

static int
sfvmParseNodeInfo(virNodeInfoPtr nodeInfo, xmlXPathContextPtr ctxt)
{
    g_autofree char *str = NULL;
    unsigned int activeCpus;
    unsigned long long memory = 0;
    int rc;

    if (virXPathUInt("string(/node/cpu/nodes[1])", ctxt, &nodeInfo->nodes) == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid node cpu nodes value"));
        return -1;
    }

    if (virXPathUInt("string(/node/cpu/sockets[1])", ctxt, &nodeInfo->sockets) == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid node cpu sockets value"));
        return -1;
    }

    if (virXPathUInt("string(/node/cpu/cores[1])", ctxt, &nodeInfo->cores) == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid node cpu cores value"));
        return -1;
    }

    if (virXPathUInt("string(/node/cpu/threads[1])", ctxt, &nodeInfo->threads) == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid node cpu threads value"));
        return -1;
    }

    nodeInfo->cpus = (nodeInfo->cores * nodeInfo->threads *
                      nodeInfo->sockets * nodeInfo->nodes);

    if ((rc = virXPathUInt("string(/node/cpu/active[1])", ctxt, &activeCpus)) == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid node cpu active value"));
        return -1;
    }

    if (rc == 0) {
        if (activeCpus < nodeInfo->cpus)
            nodeInfo->cpus = activeCpus;
    }

    if (virXPathUInt("string(/node/cpu/mhz[1])", ctxt, &nodeInfo->mhz) == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid node cpu mhz value"));
        return -1;
    }

    str = virXPathString("string(/node/cpu/model[1])", ctxt);
    if (str != NULL) {
        if (virStrcpyStatic(nodeInfo->model, str) < 0) {
            virReportError(VIR_ERR_INTERNAL_ERROR,
                           _("Model %s too big for destination"), str);
            return -1;
        }
    }

    if ((rc = virXPathULongLong("string(/node/memory[1])", ctxt, &memory)) == -2) {
        virReportError(VIR_ERR_XML_ERROR, "%s",
                       _("invalid node memory value"));
        return -1;
    }

    if (rc == 0)
        nodeInfo->memory = memory;

    return 0;
}

static int
sfvmParseDomainSnapshots(sfvmDriver *privconn,
                         virDomainObj *domobj,
                         const char *file,
                         xmlXPathContextPtr ctxt)
{
    VIR_XPATH_NODE_AUTORESTORE(ctxt)
    size_t i;
    sfvmDomainNamespaceDef *nsdata = domobj->def->namespaceData;
    xmlNodePtr *nodes = nsdata->snap_nodes;

    for (i = 0; i < nsdata->num_snap_nodes; i++) {
        virDomainMomentObj *snap;
        g_autoptr(virDomainSnapshotDef) def = NULL;
        unsigned int parseFlags = VIR_DOMAIN_SNAPSHOT_PARSE_INTERNAL |
                                  VIR_DOMAIN_SNAPSHOT_PARSE_REDEFINE;
        bool cur;

        if (!(ctxt->node = sfvmParseXMLDocFromFile(nodes[i], file)))
            return -1;

        if (!(def = virDomainSnapshotDefParse(ctxt, privconn->xmlopt, NULL,
                                              &cur, parseFlags)))
            return -1;

        if (!(snap = virDomainSnapshotAssignDef(domobj->snapshots, &def)))
            return -1;

        if (cur) {
            if (virDomainSnapshotGetCurrent(domobj->snapshots)) {
                virReportError(VIR_ERR_INTERNAL_ERROR, "%s",
                               _("more than one snapshot claims to be active"));
                return -1;
            }

            virDomainSnapshotSetCurrent(domobj->snapshots, snap);
        }
    }

    if (virDomainSnapshotUpdateRelations(domobj->snapshots) < 0) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("Snapshots have inconsistent relations for "
                         "domain %s"), domobj->def->name);
        return -1;
    }

    return 0;
}

static int
sfvmParseDomains(sfvmDriver *privconn,
                 const char *file,
                 xmlXPathContextPtr ctxt)
{
    int num, ret = -1;
    size_t i;
    virDomainObj *obj = NULL;
    g_autofree xmlNodePtr *nodes = NULL;

    num = virXPathNodeSet("/node/domain", ctxt, &nodes);
    if (num < 0)
        return -1;

    for (i = 0; i < num; i++) {
        VIR_XPATH_NODE_AUTORESTORE(ctxt)
        g_autoptr(virDomainDef) def = NULL;
        sfvmDomainNamespaceDef *nsdata;

        if (!(ctxt->node = sfvmParseXMLDocFromFile(nodes[i], file)))
            goto error;

        def = virDomainDefParseNode(ctxt, privconn->xmlopt, NULL,
                                    VIR_DOMAIN_DEF_PARSE_INACTIVE);
        if (!def)
            goto error;

        if (sfvmDomainGenerateIfnames(def) < 0 ||
            !(obj = virDomainObjListAdd(privconn->domains,
                                        &def,
                                        privconn->xmlopt,
                                        0, NULL))) {
            goto error;
        }

        if (sfvmParseDomainSnapshots(privconn, obj, file, ctxt) < 0)
            goto error;

        nsdata = obj->def->namespaceData;
        obj->persistent = !nsdata->transient;
        obj->hasManagedSave = nsdata->hasManagedSave;

        if (nsdata->runstate != VIR_DOMAIN_SHUTOFF) {
            if (sfvmDomainStartState(privconn, obj,
                                     VIR_DOMAIN_RUNNING_BOOTED) < 0)
                goto error;
        } else {
            sfvmDomainShutdownState(NULL, obj, 0);
        }
        virDomainObjSetState(obj, nsdata->runstate, 0);

        sfvmDomainObjCheckTaint(obj);

        sfvmDomainGenerateIOThreadInfos(obj);

        virDomainObjEndAPI(&obj);
    }

    ret = 0;
 error:
    virDomainObjEndAPI(&obj);
    return ret;
}


static int
sfvmParseNetworks(sfvmDriver *privconn,
                  const char *file,
                  xmlXPathContextPtr ctxt)
{
    VIR_XPATH_NODE_AUTORESTORE(ctxt)
    int num;
    size_t i;
    virNetworkObj *obj;
    g_autofree xmlNodePtr *nodes = NULL;

    num = virXPathNodeSet("/node/network", ctxt, &nodes);
    if (num < 0)
        return -1;

    for (i = 0; i < num; i++) {
        g_autoptr(virNetworkDef) def = NULL;

        if (!(ctxt->node = sfvmParseXMLDocFromFile(nodes[i], file)))
            return -1;

        if (!(def = virNetworkDefParseXML(ctxt, NULL)))
            return -1;

        if (!(obj = virNetworkObjAssignDef(privconn->networks, def, 0)))
            return -1;
        def = NULL;

        virNetworkObjSetActive(obj, true);
        virNetworkObjEndAPI(&obj);
    }

    return 0;
}


static int
sfvmParseInterfaces(sfvmDriver *privconn,
                    const char *file,
                    xmlXPathContextPtr ctxt)
{
    VIR_XPATH_NODE_AUTORESTORE(ctxt)
    int num;
    size_t i;
    virInterfaceObj *obj;
    g_autofree xmlNodePtr *nodes = NULL;

    num = virXPathNodeSet("/node/interface", ctxt, &nodes);
    if (num < 0)
        return -1;

    for (i = 0; i < num; i++) {
        g_autoptr(virInterfaceDef) def = NULL;

        if (!(ctxt->node = sfvmParseXMLDocFromFile(nodes[i], file)))
            return -1;

        if (!(def = virInterfaceDefParseXML(ctxt, VIR_INTERFACE_TYPE_LAST)))
            return -1;

        if (!(obj = virInterfaceObjListAssignDef(privconn->ifaces, &def)))
            return -1;

        virInterfaceObjSetActive(obj, true);
        virInterfaceObjEndAPI(&obj);
    }

    return 0;
}


static int
sfvmOpenVolumesForPool(const char *file,
                       xmlXPathContextPtr ctxt,
                       virStoragePoolObj *obj)
{
    VIR_XPATH_NODE_AUTORESTORE(ctxt)
    virStoragePoolDef *def = virStoragePoolObjGetDef(obj);
    size_t i;
    int num;
    g_autofree xmlNodePtr *nodes = NULL;
    g_autoptr(virStorageVolDef) volDef = NULL;

    num = virXPathNodeSet("./volume", ctxt, &nodes);
    if (num < 0)
        return -1;

    for (i = 0; i < num; i++) {
        if (!(ctxt->node = sfvmParseXMLDocFromFile(nodes[i], file)))
            return -1;

        if (!(volDef = virStorageVolDefParseXML(def, ctxt, 0)))
            return -1;

        if (!volDef->target.path) {
            volDef->target.path = g_strdup_printf("%s/%s", def->target.path,
                                                  volDef->name);
        }

        if (!volDef->key)
            volDef->key = g_strdup(volDef->target.path);

        if (virStoragePoolObjAddVol(obj, volDef) < 0)
            return -1;

        def->allocation += volDef->target.allocation;
        def->available = (def->capacity - def->allocation);
        volDef = NULL;
    }

    return 0;
}


static int
sfvmParseStorage(sfvmDriver *privconn,
                 const char *file,
                 xmlXPathContextPtr ctxt)
{
    VIR_XPATH_NODE_AUTORESTORE(ctxt)
    int num;
    size_t i;
    virStoragePoolObj *obj;
    g_autofree xmlNodePtr *nodes = NULL;

    num = virXPathNodeSet("/node/pool", ctxt, &nodes);
    if (num < 0)
        return -1;

    for (i = 0; i < num; i++) {
        virStoragePoolDef *def;

        if (!(ctxt->node = sfvmParseXMLDocFromFile(nodes[i], file)))
            return -1;

        if (!(def = virStoragePoolDefParseXML(ctxt)))
            return -1;

        if (!(obj = virStoragePoolObjListAdd(privconn->pools, &def, 0))) {
            virStoragePoolDefFree(def);
            return -1;
        }

        if (sfvmStoragePoolObjSetDefaults(obj) == -1) {
            virStoragePoolObjEndAPI(&obj);
            return -1;
        }
        virStoragePoolObjSetActive(obj, true);

        /* Find storage volumes */
        if (sfvmOpenVolumesForPool(file, ctxt, obj) < 0) {
            virStoragePoolObjEndAPI(&obj);
            return -1;
        }

        virStoragePoolObjEndAPI(&obj);
    }

    return 0;
}


static int
sfvmParseNodedevs(sfvmDriver *privconn,
                  const char *file,
                  xmlXPathContextPtr ctxt)
{
    VIR_XPATH_NODE_AUTORESTORE(ctxt)
    int num;
    size_t i;
    virNodeDeviceObj *obj;
    g_autofree xmlNodePtr *nodes = NULL;

    num = virXPathNodeSet("/node/device", ctxt, &nodes);
    if (num < 0)
        return -1;

    for (i = 0; i < num; i++) {
        virNodeDeviceDef *def;

        if (!(ctxt->node = sfvmParseXMLDocFromFile(nodes[i], file)))
            return -1;

        if (!(def = virNodeDeviceDefParseXML(ctxt, 0, NULL)))
            return -1;

        if (!(obj = virNodeDeviceObjListAssignDef(privconn->devs, def))) {
            virNodeDeviceDefFree(def);
            return -1;
        }

        virNodeDeviceObjSetSkipUpdateCaps(obj, true);
        virNodeDeviceObjEndAPI(&obj);
    }

    return 0;
}

static int
sfvmParseAuthUsers(sfvmDriver *privconn,
                   xmlXPathContextPtr ctxt)
{
    int num;
    size_t i;
    g_autofree xmlNodePtr *nodes = NULL;

    num = virXPathNodeSet("/node/auth/user", ctxt, &nodes);
    if (num < 0)
        return -1;

    privconn->numAuths = num;
    if (num)
        privconn->auths = g_new0(sfvmAuth, num);

    for (i = 0; i < num; i++) {
        g_autofree char *username = NULL;

        ctxt->node = nodes[i];
        username = virXPathString("string(.)", ctxt);
        if (!username || STREQ(username, "")) {
            virReportError(VIR_ERR_XML_ERROR, "%s",
                           _("missing username in /node/auth/user field"));
            return -1;
        }
        /* This field is optional. */
        privconn->auths[i].password = virXMLPropString(nodes[i], "password");
        privconn->auths[i].username = g_steal_pointer(&username);
    }

    return 0;
}

static int
sfvmOpenParse(sfvmDriver *privconn,
              const char *file,
              xmlXPathContextPtr ctxt)
{
    if (sfvmParseNodeInfo(&privconn->nodeInfo, ctxt) < 0)
        return -1;
    if (sfvmParseDomains(privconn, file, ctxt) < 0)
        return -1;
    if (sfvmParseNetworks(privconn, file, ctxt) < 0)
        return -1;
    if (sfvmParseInterfaces(privconn, file, ctxt) < 0)
        return -1;
    if (sfvmParseStorage(privconn, file, ctxt) < 0)
        return -1;
    if (sfvmParseNodedevs(privconn, file, ctxt) < 0)
        return -1;
    if (sfvmParseAuthUsers(privconn, ctxt) < 0)
        return -1;

    return 0;
}

/* No shared state between simultaneous sfvm connections initialized
 * from a file.  */
static int
sfvmOpenFromFile(virConnectPtr conn, const char *file)
{
    g_autoptr(xmlDoc) doc = NULL;
    g_autoptr(xmlXPathContext) ctxt = NULL;
    sfvmDriver *privconn;

    if (!(privconn = sfvmDriverNew()))
        return VIR_DRV_OPEN_ERROR;

    virObjectLock(privconn);
    conn->privateData = privconn;

    if (!(privconn->caps = sfvmBuildCapabilities(conn)))
        goto error;

    if (!(doc = virXMLParse(file, NULL, NULL, "node", &ctxt, NULL, false)))
        goto error;

    privconn->numCells = 0;
    memmove(&privconn->nodeInfo, &defaultNodeInfo, sizeof(defaultNodeInfo));

    if (sfvmOpenParse(privconn, file, ctxt) < 0)
        goto error;

    virObjectUnlock(privconn);

    return VIR_DRV_OPEN_SUCCESS;

 error:
    virObjectUnref(privconn);
    conn->privateData = NULL;
    return VIR_DRV_OPEN_ERROR;
}

/* Simultaneous sfvm:///default connections should share the same
 * common state (among other things, this allows testing event
 * detection in one connection for an action caused in another).  */
static int
sfvmOpenDefault(virConnectPtr conn)
{
    sfvmDriver *privconn = NULL;
    g_autoptr(xmlDoc) doc = NULL;
    g_autoptr(xmlXPathContext) ctxt = NULL;
    size_t i;
    VIR_LOCK_GUARD lock = virLockGuardLock(&defaultLock);

    if (defaultPrivconn) {
        conn->privateData = virObjectRef(defaultPrivconn);
        return VIR_DRV_OPEN_SUCCESS;
    }

    if (!(privconn = sfvmDriverNew()))
        goto error;

    conn->privateData = privconn;

    memmove(&privconn->nodeInfo, &defaultNodeInfo, sizeof(defaultNodeInfo));

    /* Numa setup */
    privconn->numCells = 2;
    privconn->cells = g_new0(sfvmCell, privconn->numCells);
    for (i = 0; i < privconn->numCells; i++) {
        privconn->cells[i].numCpus = 8;
        privconn->cells[i].mem = (i + 1) * 2048 * 1024;
        privconn->cells[i].freeMem = (i + 1) * 1024 * 1024;
    }
    for (i = 0; i < 16; i++) {
        virBitmap *siblings = virBitmapNew(16);
        ignore_value(virBitmapSetBit(siblings, i));
        privconn->cells[i / 8].cpus[(i % 8)].id = i;
        privconn->cells[i / 8].cpus[(i % 8)].socket_id = i / 8;
        privconn->cells[i / 8].cpus[(i % 8)].core_id = i % 8;
        privconn->cells[i / 8].cpus[(i % 8)].siblings = siblings;
    }

    if (!(privconn->caps = sfvmBuildCapabilities(conn)))
        goto error;

    if (!(doc = virXMLParse(NULL, defaultConnXML, _("(sfvm driver)"),
                            "node", &ctxt, NULL, false)))
        goto error;

    if (sfvmOpenParse(privconn, NULL, ctxt) < 0)
        goto error;

    defaultPrivconn = privconn;
    return VIR_DRV_OPEN_SUCCESS;

 error:
    virObjectUnref(privconn);
    conn->privateData = NULL;
    return VIR_DRV_OPEN_ERROR;
}

static int
sfvmConnectAuthenticate(virConnectPtr conn,
                        virConnectAuthPtr auth)
{
    sfvmDriver *privconn = conn->privateData;
    int ret = -1;
    ssize_t i;
    g_autofree char *username = NULL;
    g_autofree char *password = NULL;

    virObjectLock(privconn);
    if (privconn->numAuths == 0) {
        virObjectUnlock(privconn);
        return 0;
    }

    /* Authentication is required because the sfvm XML contains a
     * non-empty <auth/> section.  First we must ask for a username.
     */
    if (!(username = virAuthGetUsername(conn, auth, "sfvm", NULL,
                                        "localhost"/*?*/)))
        goto cleanup;

    /* Does the username exist? */
    for (i = 0; i < privconn->numAuths; ++i) {
        if (STREQ(privconn->auths[i].username, username))
            goto found_user;
    }
    i = -1;

 found_user:
    /* Even if we didn't find the user, we still ask for a password. */
    if (i == -1 || privconn->auths[i].password != NULL) {
        if (!(password = virAuthGetPassword(conn, auth, "sfvm", username,
                                            "localhost")))
            goto cleanup;
    }

    if (i == -1 ||
        (password && STRNEQ(privconn->auths[i].password, password))) {
        virReportError(VIR_ERR_AUTH_FAILED, "%s",
                       _("authentication failed, see sfvm XML for the correct username/password"));
        goto cleanup;
    }

    ret = 0;
 cleanup:
    virObjectUnlock(privconn);
    return ret;
}


static void
sfvmDriverCloseInternal(sfvmDriver *driver)
{
    VIR_LOCK_GUARD lock = virLockGuardLock(&defaultLock);

    sfvmDriverDisposed = false;
    virObjectUnref(driver);
    if (sfvmDriverDisposed && driver == defaultPrivconn)
        defaultPrivconn = NULL;
}


static virDrvOpenStatus
sfvmConnectOpen(virConnectPtr conn,
                virConnectAuthPtr auth,
                virConf *conf G_GNUC_UNUSED,
                unsigned int flags)
{
    int ret;

    virCheckFlags(VIR_CONNECT_RO, VIR_DRV_OPEN_ERROR);

    if (conn->uri->path[0] == '\0' ||
        (conn->uri->path[0] == '/' && conn->uri->path[1] == '\0')) {
        virReportError(VIR_ERR_INVALID_ARG,
                       "%s", _("sfvmOpen: supply a path or use sfvm:///default"));
        return VIR_DRV_OPEN_ERROR;
    }

    if (STREQ(conn->uri->path, "/default"))
        ret = sfvmOpenDefault(conn);
    else
        ret = sfvmOpenFromFile(conn,
                               conn->uri->path);

    if (ret != VIR_DRV_OPEN_SUCCESS)
        return ret;

    /* Fake authentication. */
    if (sfvmConnectAuthenticate(conn, auth) < 0) {
        g_clear_pointer(&conn->privateData, sfvmDriverCloseInternal);
        return VIR_DRV_OPEN_ERROR;
    }

    return VIR_DRV_OPEN_SUCCESS;
}


static int
sfvmConnectClose(virConnectPtr conn)
{
    g_clear_pointer(&conn->privateData, sfvmDriverCloseInternal);
    return 0;
}


static int sfvmConnectGetVersion(virConnectPtr conn G_GNUC_UNUSED,
                                 unsigned long *hvVer)
{
    *hvVer = 2;
    return 0;
}

static char *sfvmConnectGetHostname(virConnectPtr conn G_GNUC_UNUSED)
{
    return virGetHostname();
}


static int sfvmConnectIsSecure(virConnectPtr conn G_GNUC_UNUSED)
{
    return 1;
}

static int sfvmConnectIsEncrypted(virConnectPtr conn G_GNUC_UNUSED)
{
    return 0;
}

static int sfvmConnectIsAlive(virConnectPtr conn G_GNUC_UNUSED)
{
    return 1;
}

static int sfvmConnectGetMaxVcpus(virConnectPtr conn G_GNUC_UNUSED,
                                  const char *type G_GNUC_UNUSED)
{
    return 32;
}

static char *
sfvmConnectBaselineCPU(virConnectPtr conn G_GNUC_UNUSED,
                       const char **xmlCPUs,
                       unsigned int ncpus,
                       unsigned int flags)
{
    virCPUDef **cpus = NULL;
    virCPUDef *cpu = NULL;
    char *cpustr = NULL;

    virCheckFlags(VIR_CONNECT_BASELINE_CPU_EXPAND_FEATURES, NULL);

    if (!(cpus = virCPUDefListParse(xmlCPUs, ncpus, VIR_CPU_TYPE_HOST)))
        goto cleanup;

    if (!(cpu = virCPUBaseline(VIR_ARCH_NONE, cpus, ncpus, NULL, NULL, false)))
        goto cleanup;

    if ((flags & VIR_CONNECT_BASELINE_CPU_EXPAND_FEATURES) &&
        virCPUExpandFeatures(cpus[0]->arch, cpu) < 0)
        goto cleanup;

    cpustr = virCPUDefFormat(cpu, NULL);

 cleanup:
    virCPUDefListFree(cpus);
    virCPUDefFree(cpu);

    return cpustr;
}

static int sfvmNodeGetInfo(virConnectPtr conn,
                           virNodeInfoPtr info)
{
    sfvmDriver *privconn = conn->privateData;
    virObjectLock(privconn);
    memcpy(info, &privconn->nodeInfo, sizeof(virNodeInfo));
    virObjectUnlock(privconn);
    return 0;
}

static char *sfvmConnectGetCapabilities(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    char *xml;
    virObjectLock(privconn);
    xml = virCapabilitiesFormatXML(privconn->caps);
    virObjectUnlock(privconn);
    return xml;
}

static char *
sfvmConnectGetSysinfo(virConnectPtr conn G_GNUC_UNUSED,
                      unsigned int flags)
{
    const char *sysinfo = "<sysinfo type='smbios'>\n"
           "  <bios>\n"
           "    <entry name='vendor'>LENOVO</entry>\n"
           "    <entry name='version'>G4ETA1WW (2.61 )</entry>\n"
           "    <entry name='date'>05/07/2014</entry>\n"
           "    <entry name='release'>2.61</entry>\n"
           "  </bios>\n"
           "</sysinfo>\n";

    virCheckFlags(0, NULL);

    return g_strdup(sysinfo);
}

static const char *
sfvmConnectGetType(virConnectPtr conn G_GNUC_UNUSED)
{
    return "SFVM";
}


static int
sfvmConnectSupportsFeature(virConnectPtr conn G_GNUC_UNUSED,
                           int feature)
{
    int supported;

    if (virDriverFeatureIsGlobal(feature, &supported))
        return supported;

    switch ((virDrvFeature) feature) {
    case VIR_DRV_FEATURE_TYPED_PARAM_STRING:
    case VIR_DRV_FEATURE_NETWORK_UPDATE_HAS_CORRECT_ORDER:
        return 1;
    case VIR_DRV_FEATURE_MIGRATION_V2:
    case VIR_DRV_FEATURE_MIGRATION_V3:
    case VIR_DRV_FEATURE_MIGRATION_P2P:
    case VIR_DRV_FEATURE_MIGRATE_CHANGE_PROTECTION:
    case VIR_DRV_FEATURE_FD_PASSING:
    case VIR_DRV_FEATURE_XML_MIGRATABLE:
    case VIR_DRV_FEATURE_MIGRATION_OFFLINE:
    case VIR_DRV_FEATURE_MIGRATION_PARAMS:
    case VIR_DRV_FEATURE_MIGRATION_DIRECT:
    case VIR_DRV_FEATURE_MIGRATION_V1:
    case VIR_DRV_FEATURE_PROGRAM_KEEPALIVE:
    case VIR_DRV_FEATURE_REMOTE:
    case VIR_DRV_FEATURE_REMOTE_CLOSE_CALLBACK:
    case VIR_DRV_FEATURE_REMOTE_EVENT_CALLBACK:
    default:
        return 0;
    }
}


static int sfvmConnectNumOfDomains(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    int count;

    virObjectLock(privconn);
    count = virDomainObjListNumOfDomains(privconn->domains, true, NULL, NULL);
    virObjectUnlock(privconn);

    return count;
}

static int sfvmDomainIsActive(virDomainPtr dom)
{
    virDomainObj *obj;
    int ret;

    if (!(obj = sfvmDomObjFromDomain(dom)))
        return -1;

    ret = virDomainObjIsActive(obj);
    virDomainObjEndAPI(&obj);
    return ret;
}

static int sfvmDomainIsPersistent(virDomainPtr dom)
{
    virDomainObj *obj;
    int ret;

    if (!(obj = sfvmDomObjFromDomain(dom)))
        return -1;

    ret = obj->persistent;

    virDomainObjEndAPI(&obj);
    return ret;
}

static int sfvmDomainIsUpdated(virDomainPtr dom G_GNUC_UNUSED)
{
    return 0;
}

static virDomainPtr
sfvmDomainCreateXML(virConnectPtr conn, const char *xml,
                      unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    virDomainPtr ret = NULL;
    g_autoptr(virDomainDef) def = NULL;
    virDomainObj *dom = NULL;
    virObjectEvent *event = NULL;
    unsigned int parse_flags = VIR_DOMAIN_DEF_PARSE_INACTIVE;

    virCheckFlags(VIR_DOMAIN_START_VALIDATE, NULL);

    if (flags & VIR_DOMAIN_START_VALIDATE)
        parse_flags |= VIR_DOMAIN_DEF_PARSE_VALIDATE_SCHEMA;

    virObjectLock(privconn);
    if ((def = virDomainDefParseString(xml, privconn->xmlopt,
                                       NULL, parse_flags)) == NULL)
        goto cleanup;

    if (sfvmDomainGenerateIfnames(def) < 0)
        goto cleanup;
    if (!(dom = virDomainObjListAdd(privconn->domains,
                                    &def,
                                    privconn->xmlopt,
                                    VIR_DOMAIN_OBJ_LIST_ADD_LIVE |
                                    VIR_DOMAIN_OBJ_LIST_ADD_CHECK_LIVE,
                                    NULL)))
        goto cleanup;

    if (sfvmDomainStartState(privconn, dom, VIR_DOMAIN_RUNNING_BOOTED) < 0) {
        if (!dom->persistent)
            virDomainObjListRemove(privconn->domains, dom);
        goto cleanup;
    }

    event = virDomainEventLifecycleNewFromObj(dom,
                                     VIR_DOMAIN_EVENT_STARTED,
                                     VIR_DOMAIN_EVENT_STARTED_BOOTED);

    ret = virGetDomain(conn, dom->def->name, dom->def->uuid, dom->def->id);

 cleanup:
    virDomainObjEndAPI(&dom);
    virObjectEventStateQueue(privconn->eventState, event);
    virObjectUnlock(privconn);
    return ret;
}


static virDomainPtr
sfvmDomainCreateXMLWithFiles(virConnectPtr conn,
                             const char *xml,
                             unsigned int nfiles G_GNUC_UNUSED,
                             int *files G_GNUC_UNUSED,
                             unsigned int flags)
{
    return sfvmDomainCreateXML(conn, xml, flags);
}


static virDomainPtr sfvmDomainLookupByID(virConnectPtr conn,
                                         int id)
{
    sfvmDriver *privconn = conn->privateData;
    virDomainPtr ret = NULL;
    virDomainObj *dom;

    if (!(dom = virDomainObjListFindByID(privconn->domains, id))) {
        virReportError(VIR_ERR_NO_DOMAIN, NULL);
        return NULL;
    }

    ret = virGetDomain(conn, dom->def->name, dom->def->uuid, dom->def->id);

    virDomainObjEndAPI(&dom);
    return ret;
}

static virDomainPtr sfvmDomainLookupByUUID(virConnectPtr conn,
                                           const unsigned char *uuid)
{
    sfvmDriver *privconn = conn->privateData;
    virDomainPtr ret = NULL;
    virDomainObj *dom;

    if (!(dom = virDomainObjListFindByUUID(privconn->domains, uuid))) {
        virReportError(VIR_ERR_NO_DOMAIN, NULL);
        return NULL;
    }

    ret = virGetDomain(conn, dom->def->name, dom->def->uuid, dom->def->id);

    virDomainObjEndAPI(&dom);
    return ret;
}

static virDomainPtr sfvmDomainLookupByName(virConnectPtr conn,
                                           const char *name)
{
    sfvmDriver *privconn = conn->privateData;
    virDomainPtr ret = NULL;
    virDomainObj *dom;

    if (!(dom = virDomainObjListFindByName(privconn->domains, name))) {
        virReportError(VIR_ERR_NO_DOMAIN, NULL);
        goto cleanup;
    }

    ret = virGetDomain(conn, dom->def->name, dom->def->uuid, dom->def->id);

 cleanup:
    virDomainObjEndAPI(&dom);
    return ret;
}

static int sfvmConnectListDomains(virConnectPtr conn,
                                  int *ids,
                                  int maxids)
{
    sfvmDriver *privconn = conn->privateData;

    return virDomainObjListGetActiveIDs(privconn->domains, ids, maxids,
                                        NULL, NULL);
}

static int sfvmDomainDestroyFlags(virDomainPtr domain,
                                  unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_DESTROY_GRACEFUL, -1);

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjCheckActive(privdom) < 0)
        goto cleanup;

    sfvmDomainShutdownState(domain, privdom, VIR_DOMAIN_SHUTOFF_DESTROYED);
    event = virDomainEventLifecycleNewFromObj(privdom,
                                     VIR_DOMAIN_EVENT_STOPPED,
                                     VIR_DOMAIN_EVENT_STOPPED_DESTROYED);

    if (!privdom->persistent)
        virDomainObjListRemove(privconn->domains, privdom);

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}

static int sfvmDomainDestroy(virDomainPtr domain)
{
    return sfvmDomainDestroyFlags(domain, 0);
}

static int sfvmDomainResume(virDomainPtr domain)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    if (virDomainObjGetState(privdom, NULL) != VIR_DOMAIN_PAUSED) {
        virReportError(VIR_ERR_INTERNAL_ERROR, _("domain '%s' not paused"),
                       domain->name);
        goto cleanup;
    }

    virDomainObjSetState(privdom, VIR_DOMAIN_RUNNING,
                         VIR_DOMAIN_RUNNING_UNPAUSED);
    event = virDomainEventLifecycleNewFromObj(privdom,
                                     VIR_DOMAIN_EVENT_RESUMED,
                                     VIR_DOMAIN_EVENT_RESUMED_UNPAUSED);
    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}

static int sfvmDomainSuspend(virDomainPtr domain)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;
    int state;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    state = virDomainObjGetState(privdom, NULL);
    if (state == VIR_DOMAIN_SHUTOFF || state == VIR_DOMAIN_PAUSED) {
        virReportError(VIR_ERR_INTERNAL_ERROR, _("fpga domain '%s' not running"),
                       domain->name);
        goto cleanup;
    }

    virDomainObjSetState(privdom, VIR_DOMAIN_PAUSED, VIR_DOMAIN_PAUSED_USER);
    event = virDomainEventLifecycleNewFromObj(privdom,
                                     VIR_DOMAIN_EVENT_SUSPENDED,
                                     VIR_DOMAIN_EVENT_SUSPENDED_PAUSED);
    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}


static void
sfvmDomainActionSetState(virDomainObj *dom,
                         int lifecycle_type)
{
    switch (lifecycle_type) {
    case VIR_DOMAIN_LIFECYCLE_ACTION_DESTROY:
        virDomainObjSetState(dom, VIR_DOMAIN_SHUTOFF,
                             VIR_DOMAIN_SHUTOFF_SHUTDOWN);
        break;

    case VIR_DOMAIN_LIFECYCLE_ACTION_RESTART:
        virDomainObjSetState(dom, VIR_DOMAIN_RUNNING,
                             VIR_DOMAIN_RUNNING_BOOTED);
        break;

    case VIR_DOMAIN_LIFECYCLE_ACTION_PRESERVE:
        virDomainObjSetState(dom, VIR_DOMAIN_SHUTOFF,
                             VIR_DOMAIN_SHUTOFF_SHUTDOWN);
        break;

    case VIR_DOMAIN_LIFECYCLE_ACTION_RESTART_RENAME:
        virDomainObjSetState(dom, VIR_DOMAIN_RUNNING,
                             VIR_DOMAIN_RUNNING_BOOTED);
        break;

    default:
        virDomainObjSetState(dom, VIR_DOMAIN_SHUTOFF,
                             VIR_DOMAIN_SHUTOFF_SHUTDOWN);
        break;
    }
}


static int sfvmDomainShutdownFlags(virDomainPtr domain,
                                   unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(0, -1);


    if (!(privdom = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjGetState(privdom, NULL) == VIR_DOMAIN_SHUTOFF) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("domain '%s' not running"), domain->name);
        goto cleanup;
    }

    sfvmDomainActionSetState(privdom, privdom->def->onPoweroff);

    if (virDomainObjGetState(privdom, NULL) == VIR_DOMAIN_SHUTOFF) {
        sfvmDomainShutdownState(domain, privdom, VIR_DOMAIN_SHUTOFF_SHUTDOWN);
        event = virDomainEventLifecycleNewFromObj(privdom,
                                                  VIR_DOMAIN_EVENT_STOPPED,
                                                  VIR_DOMAIN_EVENT_STOPPED_SHUTDOWN);

        if (!privdom->persistent)
            virDomainObjListRemove(privconn->domains, privdom);
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}

static int sfvmDomainShutdown(virDomainPtr domain)
{
    return sfvmDomainShutdownFlags(domain, 0);
}

/* Similar behaviour as shutdown */
static int sfvmDomainReboot(virDomainPtr domain,
                            unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_REBOOT_DEFAULT |
                  VIR_DOMAIN_REBOOT_ACPI_POWER_BTN |
                  VIR_DOMAIN_REBOOT_GUEST_AGENT |
                  VIR_DOMAIN_REBOOT_INITCTL |
                  VIR_DOMAIN_REBOOT_SIGNAL |
                  VIR_DOMAIN_REBOOT_PARAVIRT, -1);

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjCheckActive(privdom) < 0)
        goto cleanup;

    sfvmDomainActionSetState(privdom, privdom->def->onReboot);

    if (virDomainObjGetState(privdom, NULL) == VIR_DOMAIN_SHUTOFF) {
        sfvmDomainShutdownState(domain, privdom, VIR_DOMAIN_SHUTOFF_SHUTDOWN);
        event = virDomainEventLifecycleNewFromObj(privdom,
                                         VIR_DOMAIN_EVENT_STOPPED,
                                         VIR_DOMAIN_EVENT_STOPPED_SHUTDOWN);

        if (!privdom->persistent)
            virDomainObjListRemove(privconn->domains, privdom);
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}


static int
sfvmDomainReset(virDomainPtr dom,
                unsigned int flags)
{
    virDomainObj *vm;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static char *
sfvmDomainGetHostname(virDomainPtr domain,
                      unsigned int flags)
{
    char *ret = NULL;
    virDomainObj *vm = NULL;

    virCheckFlags(0, NULL);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    ret = g_strdup_printf("%shost", domain->name);

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int sfvmDomainGetInfo(virDomainPtr domain,
                             virDomainInfoPtr info)
{
    virDomainObj *privdom;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    info->state = virDomainObjGetState(privdom, NULL);
    info->memory = privdom->def->mem.cur_balloon;
    info->maxMem = virDomainDefGetMemoryTotal(privdom->def);
    info->nrVirtCpu = virDomainDefGetVcpus(privdom->def);
    info->cpuTime = g_get_real_time() * 1000;

    virDomainObjEndAPI(&privdom);
    return 0;
}

static int
sfvmDomainGetState(virDomainPtr domain,
                   int *state,
                   int *reason,
                   unsigned int flags)
{
    virDomainObj *privdom;

    virCheckFlags(0, -1);

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    *state = virDomainObjGetState(privdom, reason);

    virDomainObjEndAPI(&privdom);

    return 0;
}

static int
sfvmDomainGetControlInfo(virDomainPtr dom,
                         virDomainControlInfoPtr info,
                         unsigned int flags)
{
    virDomainObj *vm;
    sfvmDomainObjPrivate *priv;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    priv = vm->privateData;

    memset(info, 0, sizeof(*info));

    if (priv->seconds > 0 && priv->seconds < 10000) {
        info->state = VIR_DOMAIN_CONTROL_JOB;
        info->stateTime = priv->seconds;
    } else if (priv->seconds < 30000 && priv->seconds >= 10000) {
        info->state = VIR_DOMAIN_CONTROL_OCCUPIED;
        info->stateTime = priv->seconds - 10000;
    } else if (priv->seconds < 60000 && priv->seconds >= 30000) {
        info->state = VIR_DOMAIN_CONTROL_ERROR;
        switch (priv->seconds % 4) {
        case 0:
            info->details = VIR_DOMAIN_CONTROL_ERROR_REASON_NONE;
            break;

        case 1:
            info->details = VIR_DOMAIN_CONTROL_ERROR_REASON_UNKNOWN;
            break;

        case 2:
            info->details = VIR_DOMAIN_CONTROL_ERROR_REASON_MONITOR;
            break;

        case 3:
            info->details = VIR_DOMAIN_CONTROL_ERROR_REASON_INTERNAL;
            break;

        default:
            info->details = VIR_DOMAIN_CONTROL_ERROR_REASON_NONE;
            break;
        }
        info->stateTime = priv->seconds - 30000;
    } else {
        info->state = VIR_DOMAIN_CONTROL_OK;
    }

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainGetTime(virDomainPtr dom,
                  long long *seconds,
                  unsigned int *nseconds,
                  unsigned int flags)
{
    virDomainObj *vm = NULL;
    sfvmDomainObjPrivate *priv;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjGetState(vm, NULL) != VIR_DOMAIN_RUNNING) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("domain is not running"));
        goto cleanup;
    }

    priv = vm->privateData;
    *seconds = priv->seconds;
    *nseconds = priv->nseconds;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSetTime(virDomainPtr dom,
                  long long seconds,
                  unsigned int nseconds,
                  unsigned int flags)
{
    virDomainObj *vm = NULL;
    sfvmDomainObjPrivate *priv;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_TIME_SYNC, ret);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    priv = vm->privateData;
    priv->seconds = seconds;
    priv->nseconds = nseconds;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

#define TEST_SAVE_MAGIC "TestGuestMagic"


/**
 * sfvmDomainSaveImageWrite:
 * @driver: sfvm driver data
 * @def: domain definition whose XML will be stored in the image
 * @path: path to the saved image
 *
 * Returns true on success, else false.
 */
static bool
sfvmDomainSaveImageWrite(sfvmDriver *driver,
                         const char *path,
                         virDomainDef *def)
{
    int len;
    int fd = -1;
    g_autofree char *xml = NULL;

    xml = virDomainDefFormat(def, driver->xmlopt,
                             VIR_DOMAIN_DEF_FORMAT_SECURE);

    if (xml == NULL) {
        virReportSystemError(errno,
                             _("saving domain '%s' failed to allocate space for metadata"),
                             def->name);
        goto error;
    }

    if ((fd = open(path, O_CREAT|O_TRUNC|O_WRONLY, S_IRUSR|S_IWUSR)) < 0) {
        virReportSystemError(errno,
                             _("saving domain '%s' to '%s': open failed"),
                             def->name, path);
        goto error;
    }

    if (safewrite(fd, TEST_SAVE_MAGIC, sizeof(TEST_SAVE_MAGIC)) < 0) {
        virReportSystemError(errno,
                             _("saving domain '%s' to '%s': write failed"),
                             def->name, path);
        goto error;
    }

    len = strlen(xml);
    if (safewrite(fd, (char*)&len, sizeof(len)) < 0) {
        virReportSystemError(errno,
                             _("saving domain '%s' to '%s': write failed"),
                             def->name, path);
        goto error;
    }

    if (safewrite(fd, xml, len) < 0) {
        virReportSystemError(errno,
                             _("saving domain '%s' to '%s': write failed"),
                             def->name, path);
        goto error;
    }

    if (VIR_CLOSE(fd) < 0) {
        virReportSystemError(errno,
                             _("saving domain '%s' to '%s': write failed"),
                             def->name, path);
        goto error;
    }

    return true;

 error:
    /* Don't report failure in close or unlink, because
     * in either case we're already in a failure scenario
     * and have reported an earlier error */
    VIR_FORCE_CLOSE(fd);
    unlink(path);

    return false;
}


/**
 * sfvmDomainSaveImageOpen:
 * @driver: sfvm driver data
 * @path: path of the saved image
 * @ret_def: returns domain definition created from the XML stored in the image
 *
 * Returns the opened fd of the save image file and fills ret_def on success.
 * Returns -1, on error.
 */
static int ATTRIBUTE_NONNULL(3)
sfvmDomainSaveImageOpen(sfvmDriver *driver,
                        const char *path,
                        virDomainDef **ret_def)
{
    char magic[15];
    int fd = -1;
    int len;
    g_autoptr(virDomainDef) def = NULL;
    g_autofree char *xml = NULL;

    if ((fd = open(path, O_RDONLY)) < 0) {
        virReportSystemError(errno, _("cannot read domain image '%s'"), path);
        goto error;
    }

    if (saferead(fd, magic, sizeof(magic)) != sizeof(magic)) {
        virReportSystemError(errno, _("incomplete save header in '%s'"), path);
        goto error;
    }

    if (memcmp(magic, TEST_SAVE_MAGIC, sizeof(magic))) {
        virReportError(VIR_ERR_INTERNAL_ERROR, "%s", _("mismatched header magic"));
        goto error;
    }

    if (saferead(fd, (char*)&len, sizeof(len)) != sizeof(len)) {
        virReportSystemError(errno,
                             _("failed to read metadata length in '%s'"),
                             path);
        goto error;
    }

    if (len < 1 || len > 8192) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       "%s", _("length of metadata out of range"));
        goto error;
    }

    xml = g_new0(char, len + 1);

    if (saferead(fd, xml, len) != len) {
        virReportSystemError(errno, _("incomplete metadata in '%s'"), path);
        goto error;
    }
    xml[len] = '\0';

    if (!(def = virDomainDefParseString(xml, driver->xmlopt, NULL,
                                        VIR_DOMAIN_DEF_PARSE_INACTIVE |
                                        VIR_DOMAIN_DEF_PARSE_SKIP_VALIDATE)))
        goto error;

    *ret_def = g_steal_pointer(&def);
    return fd;

 error:
    VIR_FORCE_CLOSE(fd);
    return -1;
}


static int
sfvmDomainSaveFlags(virDomainPtr domain, const char *path,
                    const char *dxml, unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(0, -1);

    if (dxml) {
        virReportError(VIR_ERR_ARGUMENT_UNSUPPORTED, "%s",
                       _("xml modification unsupported"));
        return -1;
    }

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjCheckActive(privdom) < 0)
        goto cleanup;

    if (!sfvmDomainSaveImageWrite(privconn, path, privdom->def))
        goto cleanup;

    sfvmDomainShutdownState(domain, privdom, VIR_DOMAIN_SHUTOFF_SAVED);
    event = virDomainEventLifecycleNewFromObj(privdom,
                                     VIR_DOMAIN_EVENT_STOPPED,
                                     VIR_DOMAIN_EVENT_STOPPED_SAVED);

    if (!privdom->persistent)
        virDomainObjListRemove(privconn->domains, privdom);

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}

static int
sfvmDomainSave(virDomainPtr domain,
               const char *path)
{
    return sfvmDomainSaveFlags(domain, path, NULL, 0);
}

static int
sfvmDomainRestoreFlags(virConnectPtr conn,
                       const char *path,
                       const char *dxml,
                       unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    int fd = -1;
    g_autoptr(virDomainDef) def = NULL;
    virDomainObj *dom = NULL;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(0, -1);
    if (dxml) {
        virReportError(VIR_ERR_ARGUMENT_UNSUPPORTED, "%s",
                       _("xml modification unsupported"));
        return -1;
    }

    if ((fd = sfvmDomainSaveImageOpen(privconn, path, &def)) < 0)
        goto cleanup;

    if (sfvmDomainGenerateIfnames(def) < 0)
        goto cleanup;
    if (!(dom = virDomainObjListAdd(privconn->domains,
                                    &def,
                                    privconn->xmlopt,
                                    VIR_DOMAIN_OBJ_LIST_ADD_LIVE |
                                    VIR_DOMAIN_OBJ_LIST_ADD_CHECK_LIVE,
                                    NULL)))
        goto cleanup;

    if (sfvmDomainStartState(privconn, dom, VIR_DOMAIN_RUNNING_RESTORED) < 0) {
        if (!dom->persistent)
            virDomainObjListRemove(privconn->domains, dom);
        goto cleanup;
    }

    event = virDomainEventLifecycleNewFromObj(dom,
                                     VIR_DOMAIN_EVENT_STARTED,
                                     VIR_DOMAIN_EVENT_STARTED_RESTORED);
    ret = 0;

 cleanup:
    VIR_FORCE_CLOSE(fd);
    virDomainObjEndAPI(&dom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}

static int
sfvmDomainRestore(virConnectPtr conn,
                  const char *path)
{
    return sfvmDomainRestoreFlags(conn, path, NULL, 0);
}


static int
sfvmDomainSaveImageDefineXML(virConnectPtr conn,
                             const char *path,
                             const char *dxml,
                             unsigned int flags)
{
    int fd = -1;
    g_autoptr(virDomainDef) def = NULL;
    g_autoptr(virDomainDef) newdef = NULL;
    sfvmDriver *privconn = conn->privateData;

    virCheckFlags(VIR_DOMAIN_SAVE_RUNNING |
                  VIR_DOMAIN_SAVE_PAUSED, -1);

    if ((fd = sfvmDomainSaveImageOpen(privconn, path, &def)) < 0)
        return -1;
    VIR_FORCE_CLOSE(fd);

    if ((newdef = virDomainDefParseString(dxml, privconn->xmlopt, NULL,
                                          VIR_DOMAIN_DEF_PARSE_INACTIVE)) == NULL)
        return -1;

    if (!sfvmDomainSaveImageWrite(privconn, path, newdef))
        return -1;

    return 0;
}


static char *
sfvmDomainSaveImageGetXMLDesc(virConnectPtr conn,
                              const char *path,
                              unsigned int flags)
{
    int fd = -1;
    char *ret = NULL;
    g_autoptr(virDomainDef) def = NULL;
    sfvmDriver *privconn = conn->privateData;

    virCheckFlags(VIR_DOMAIN_SAVE_IMAGE_XML_SECURE, NULL);

    if ((fd = sfvmDomainSaveImageOpen(privconn, path, &def)) < 0)
        goto cleanup;

    ret = virDomainDefFormat(def, privconn->xmlopt,
                             VIR_DOMAIN_DEF_FORMAT_SECURE);

 cleanup:
    VIR_FORCE_CLOSE(fd);
    return ret;
}


static int sfvmDomainCoreDumpWithFormat(virDomainPtr domain,
                                        const char *to,
                                        unsigned int dumpformat,
                                        unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    int fd = -1;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(VIR_DUMP_CRASH, -1);


    if (!(privdom = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjCheckActive(privdom) < 0)
        goto cleanup;

    if ((fd = open(to, O_CREAT|O_TRUNC|O_WRONLY, S_IRUSR|S_IWUSR)) < 0) {
        virReportSystemError(errno,
                             _("domain '%s' coredump: failed to open %s"),
                             domain->name, to);
        goto cleanup;
    }
    if (safewrite(fd, TEST_SAVE_MAGIC, sizeof(TEST_SAVE_MAGIC)) < 0) {
        virReportSystemError(errno,
                             _("domain '%s' coredump: failed to write header to %s"),
                             domain->name, to);
        goto cleanup;
    }
    if (VIR_CLOSE(fd) < 0) {
        virReportSystemError(errno,
                             _("domain '%s' coredump: write failed: %s"),
                             domain->name, to);
        goto cleanup;
    }

    /* we don't support non-raw formats in sfvm driver */
    if (dumpformat != VIR_DOMAIN_CORE_DUMP_FORMAT_RAW) {
        virReportError(VIR_ERR_OPERATION_UNSUPPORTED, "%s",
                       _("kdump-compressed format is not supported here"));
        goto cleanup;
    }

    if (flags & VIR_DUMP_CRASH) {
        sfvmDomainShutdownState(domain, privdom, VIR_DOMAIN_SHUTOFF_CRASHED);
        event = virDomainEventLifecycleNewFromObj(privdom,
                                         VIR_DOMAIN_EVENT_STOPPED,
                                         VIR_DOMAIN_EVENT_STOPPED_CRASHED);
        if (!privdom->persistent)
            virDomainObjListRemove(privconn->domains, privdom);
    }

    ret = 0;
 cleanup:
    VIR_FORCE_CLOSE(fd);
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}


static int
sfvmDomainCoreDump(virDomainPtr domain,
                   const char *to,
                   unsigned int flags)
{
    return sfvmDomainCoreDumpWithFormat(domain, to,
                                        VIR_DOMAIN_CORE_DUMP_FORMAT_RAW, flags);
}


static char *
sfvmDomainGetOSType(virDomainPtr dom G_GNUC_UNUSED)
{
    return g_strdup("linux");
}


static int
sfvmDomainGetLaunchSecurityInfo(virDomainPtr domain G_GNUC_UNUSED,
                                virTypedParameterPtr *params G_GNUC_UNUSED,
                                int *nparams,
                                unsigned int flags)
{
    virCheckFlags(0, -1);

    *nparams = 0;
    return 0;
}


static unsigned long long
sfvmDomainGetMaxMemory(virDomainPtr domain)
{
    virDomainObj *privdom;
    unsigned long long ret = 0;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return 0;

    ret = virDomainDefGetMemoryTotal(privdom->def);

    virDomainObjEndAPI(&privdom);
    return ret;
}



static int sfvmDomainSetMemoryStatsPeriod(virDomainPtr dom,
                                          int period,
                                          unsigned int flags)
{
    virDomainObj *vm;
    virDomainDef *def;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (!virDomainDefHasMemballoon(def)) {
        virReportError(VIR_ERR_INTERNAL_ERROR, "%s",
                       _("No memory balloon device configured, "
                         "can not set the collection period"));
        goto cleanup;
    }

    def->memballoon->period = period;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int sfvmDomainSetMemoryFlags(virDomainPtr domain,
                                    unsigned long memory,
                                    unsigned int flags)
{
    virDomainObj *vm;
    virDomainDef *def;
    int ret = -1;
    bool live = false;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_DOMAIN_MEM_MAXIMUM, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    if (!(def = virDomainObjGetOneDefState(vm, flags, &live)))
        goto cleanup;

    if (flags & VIR_DOMAIN_MEM_MAXIMUM) {
        if (live) {
            virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                           _("cannot resize the maximum memory on an "
                             "active domain"));
            goto cleanup;
        }

        if (virDomainNumaGetNodeCount(def->numa) > 0) {
            virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                           _("initial memory size of a domain with NUMA "
                             "nodes cannot be modified with this API"));
            goto cleanup;
        }

        if (def->mem.max_memory && def->mem.max_memory < memory) {
            virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                           _("cannot set initial memory size greater than "
                             "the maximum memory size"));
            goto cleanup;
        }

        virDomainDefSetMemoryTotal(def, memory);

        if (def->mem.cur_balloon > memory)
            def->mem.cur_balloon = memory;
    } else {
        if (memory > virDomainDefGetMemoryTotal(def)) {
            virReportError(VIR_ERR_INVALID_ARG, "%s",
                           _("cannot set memory higher than max memory"));
            goto cleanup;
        }

        def->mem.cur_balloon = memory;
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int sfvmDomainSetMemory(virDomainPtr domain,
                               unsigned long memory)
{
    return sfvmDomainSetMemoryFlags(domain, memory, VIR_DOMAIN_AFFECT_LIVE);
}


static int sfvmDomainSetMaxMemory(virDomainPtr domain,
                                  unsigned long memory)
{
    return sfvmDomainSetMemoryFlags(domain, memory, VIR_DOMAIN_MEM_MAXIMUM);
}


static int
sfvmDomainPinEmulator(virDomainPtr dom,
                      unsigned char *cpumap,
                      int maplen,
                      unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    g_autoptr(virBitmap) pcpumap = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (!(pcpumap = virBitmapNewData(cpumap, maplen)))
        goto cleanup;

    if (virBitmapIsAllClear(pcpumap)) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("Empty cpu list for pinning"));
        goto cleanup;
    }

    virBitmapFree(def->cputune.emulatorpin);
    def->cputune.emulatorpin = g_steal_pointer(&pcpumap);

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetEmulatorPinInfo(virDomainPtr dom,
                             unsigned char *cpumaps,
                             int maplen,
                             unsigned int flags)
{
    sfvmDriver *driver = dom->conn->privateData;
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    virBitmap *cpumask = NULL;
    g_autoptr(virBitmap) bitmap = NULL;
    int hostcpus;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    hostcpus = VIR_NODEINFO_MAXCPUS(driver->nodeInfo);

    if (def->cputune.emulatorpin) {
        cpumask = def->cputune.emulatorpin;
    } else if (def->cpumask) {
        cpumask = def->cpumask;
    } else {
        bitmap = virBitmapNew(hostcpus);
        virBitmapSetAll(bitmap);
        cpumask = bitmap;
    }

    virBitmapToDataBuf(cpumask, cpumaps, maplen);

    ret = 1;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetVcpusFlags(virDomainPtr domain, unsigned int flags)
{
    virDomainObj *vm;
    virDomainDef *def;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_DOMAIN_VCPU_MAXIMUM, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (flags & VIR_DOMAIN_VCPU_MAXIMUM)
        ret = virDomainDefGetVcpusMax(def);
    else
        ret = virDomainDefGetVcpus(def);

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainGetMaxVcpus(virDomainPtr domain)
{
    return sfvmDomainGetVcpusFlags(domain, (VIR_DOMAIN_AFFECT_LIVE |
                                            VIR_DOMAIN_VCPU_MAXIMUM));
}

static int
sfvmDomainSetVcpusFlags(virDomainPtr domain, unsigned int nrCpus,
                        unsigned int flags)
{
    sfvmDriver *driver = domain->conn->privateData;
    virDomainObj *privdom = NULL;
    virDomainDef *def;
    virDomainDef *persistentDef;
    int ret = -1, maxvcpus;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_DOMAIN_VCPU_MAXIMUM, -1);

    if ((maxvcpus = sfvmConnectGetMaxVcpus(domain->conn, NULL)) < 0)
        return -1;

    if (nrCpus > maxvcpus) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("requested cpu amount exceeds maximum supported amount "
                         "(%d > %d)"), nrCpus, maxvcpus);
        return -1;
    }

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    if (virDomainObjGetDefs(privdom, flags, &def, &persistentDef) < 0)
        goto cleanup;

    if (def && virDomainDefGetVcpusMax(def) < nrCpus) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("requested cpu amount exceeds maximum (%d > %d)"),
                       nrCpus, virDomainDefGetVcpusMax(def));
        goto cleanup;
    }

    if (persistentDef &&
        !(flags & VIR_DOMAIN_VCPU_MAXIMUM) &&
        virDomainDefGetVcpusMax(persistentDef) < nrCpus) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("requested cpu amount exceeds maximum (%d > %d)"),
                       nrCpus, virDomainDefGetVcpusMax(persistentDef));
        goto cleanup;
    }

    if (def &&
        virDomainDefSetVcpus(def, nrCpus) < 0)
        goto cleanup;

    if (persistentDef) {
        if (flags & VIR_DOMAIN_VCPU_MAXIMUM) {
            if (virDomainDefSetVcpusMax(persistentDef, nrCpus,
                                        driver->xmlopt) < 0)
                goto cleanup;
        } else {
            if (virDomainDefSetVcpus(persistentDef, nrCpus) < 0)
                goto cleanup;
        }
    }

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    return ret;
}


static int
sfvmDomainSetUserPassword(virDomainPtr dom,
                          const char *user G_GNUC_UNUSED,
                          const char *password G_GNUC_UNUSED,
                          unsigned int flags)
{
    int ret = -1;
    virDomainObj *vm;

    virCheckFlags(VIR_DOMAIN_PASSWORD_ENCRYPTED, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSetVcpus(virDomainPtr domain, unsigned int nrCpus)
{
    return sfvmDomainSetVcpusFlags(domain, nrCpus, VIR_DOMAIN_AFFECT_LIVE);
}

static int sfvmDomainGetVcpus(virDomainPtr domain,
                              virVcpuInfoPtr info,
                              int maxinfo,
                              unsigned char *cpumaps,
                              int maplen)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virDomainDef *def;
    size_t i;
    int hostcpus;
    int ret = -1;
    unsigned long long statbase;
    g_autoptr(virBitmap) allcpumap = NULL;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    if (!virDomainObjIsActive(privdom)) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       "%s", _("cannot list vcpus for an inactive domain"));
        goto cleanup;
    }

    def = privdom->def;

    statbase = g_get_real_time();

    hostcpus = VIR_NODEINFO_MAXCPUS(privconn->nodeInfo);
    allcpumap = virBitmapNew(hostcpus);
    virBitmapSetAll(allcpumap);

    /* Clamp to actual number of vcpus */
    if (maxinfo > virDomainDefGetVcpus(privdom->def))
        maxinfo = virDomainDefGetVcpus(privdom->def);

    memset(info, 0, sizeof(*info) * maxinfo);
    memset(cpumaps, 0, maxinfo * maplen);

    for (i = 0; i < maxinfo; i++) {
        virDomainVcpuDef *vcpu = virDomainDefGetVcpu(def, i);
        virBitmap *bitmap = NULL;

        if (!vcpu->online)
            continue;

        if (vcpu->cpumask)
            bitmap = vcpu->cpumask;
        else if (def->cpumask)
            bitmap = def->cpumask;
        else
            bitmap = allcpumap;

        if (cpumaps)
            virBitmapToDataBuf(bitmap, VIR_GET_CPUMAP(cpumaps, maplen, i), maplen);

        info[i].number = i;
        info[i].state = VIR_VCPU_RUNNING;
        info[i].cpu = virBitmapLastSetBit(bitmap);

        /* Fake an increasing cpu time value */
        info[i].cpuTime = statbase / 10;
    }

    ret = maxinfo;
 cleanup:
    virDomainObjEndAPI(&privdom);
    return ret;
}

static int sfvmDomainPinVcpuFlags(virDomainPtr domain,
                                  unsigned int vcpu,
                                  unsigned char *cpumap,
                                  int maplen,
                                  unsigned int flags)
{
    virDomainVcpuDef *vcpuinfo;
    virDomainObj *privdom;
    virDomainDef *def;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    def = privdom->def;

    if (!virDomainObjIsActive(privdom)) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       "%s", _("cannot pin vcpus on an inactive domain"));
        goto cleanup;
    }

    if (!(vcpuinfo = virDomainDefGetVcpu(def, vcpu)) ||
        !vcpuinfo->online) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("requested vcpu '%d' is not present in the domain"),
                       vcpu);
        goto cleanup;
    }

    virBitmapFree(vcpuinfo->cpumask);

    if (!(vcpuinfo->cpumask = virBitmapNewData(cpumap, maplen)))
        goto cleanup;

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    return ret;
}

static int sfvmDomainPinVcpu(virDomainPtr domain,
                             unsigned int vcpu,
                             unsigned char *cpumap,
                             int maplen)
{
    return sfvmDomainPinVcpuFlags(domain, vcpu, cpumap, maplen, 0);
}

static int
sfvmDomainGetVcpuPinInfo(virDomainPtr dom,
                        int ncpumaps,
                        unsigned char *cpumaps,
                        int maplen,
                        unsigned int flags)
{
    sfvmDriver *driver = dom->conn->privateData;
    virDomainObj *privdom;
    virDomainDef *def;
    g_autoptr(virBitmap) hostcpus = NULL;
    int ret = -1;

    if (!(privdom = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(privdom, flags)))
        goto cleanup;

    hostcpus = virBitmapNew(VIR_NODEINFO_MAXCPUS(driver->nodeInfo));
    virBitmapSetAll(hostcpus);

    ret = virDomainDefGetVcpuPinInfoHelper(def, maplen, ncpumaps, cpumaps,
                                           hostcpus, NULL);

 cleanup:
    virDomainObjEndAPI(&privdom);
    return ret;
}

static int
sfvmDomainRenameCallback(virDomainObj *privdom,
                         const char *new_name,
                         unsigned int flags,
                         void *opaque)
{
    sfvmDriver *driver = opaque;
    virObjectEvent *event_new = NULL;
    virObjectEvent *event_old = NULL;
    int ret = -1;
    g_autofree char *new_dom_name = NULL;

    virCheckFlags(0, -1);

    if (strchr(new_name, '/')) {
        virReportError(VIR_ERR_XML_ERROR,
                       _("name %s cannot contain '/'"), new_name);
        return -1;
    }

    new_dom_name = g_strdup(new_name);

    event_old = virDomainEventLifecycleNewFromObj(privdom,
                                                  VIR_DOMAIN_EVENT_UNDEFINED,
                                                  VIR_DOMAIN_EVENT_UNDEFINED_RENAMED);

    /* Switch name in domain definition. */
    VIR_FREE(privdom->def->name);
    privdom->def->name = g_steal_pointer(&new_dom_name);

    event_new = virDomainEventLifecycleNewFromObj(privdom,
                                                  VIR_DOMAIN_EVENT_DEFINED,
                                                  VIR_DOMAIN_EVENT_DEFINED_RENAMED);
    ret = 0;

    virObjectEventStateQueue(driver->eventState, event_old);
    virObjectEventStateQueue(driver->eventState, event_new);
    return ret;
}

static int
sfvmDomainRename(virDomainPtr dom,
                 const char *new_name,
                 unsigned int flags)
{
    sfvmDriver *driver = dom->conn->privateData;
    virDomainObj *privdom = NULL;
    int ret = -1;

    virCheckFlags(0, ret);

    if (!(privdom = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (virDomainObjIsActive(privdom)) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("cannot rename active domain"));
        goto cleanup;
    }

    if (!privdom->persistent) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("cannot rename a transient domain"));
        goto cleanup;
    }

    if (virDomainObjGetState(privdom, NULL) != VIR_DOMAIN_SHUTOFF) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       "%s", _("domain has to be shutoff before renaming"));
        goto cleanup;
    }

    if (virDomainObjListRename(driver->domains, privdom, new_name, flags,
                               sfvmDomainRenameCallback, driver) < 0)
        goto cleanup;

    /* Success, domain has been renamed. */
    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    return ret;
}

static char *sfvmDomainGetXMLDesc(virDomainPtr domain, unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainDef *def;
    virDomainObj *privdom;
    char *ret = NULL;

    virCheckFlags(VIR_DOMAIN_XML_COMMON_FLAGS, NULL);

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return NULL;

    def = (flags & VIR_DOMAIN_XML_INACTIVE) &&
        privdom->newDef ? privdom->newDef : privdom->def;

    ret = virDomainDefFormat(def, privconn->xmlopt,
                             virDomainDefFormatConvertXMLFlags(flags));

    virDomainObjEndAPI(&privdom);
    return ret;
}

static int
sfvmDomainSetBlkioParameters(virDomainPtr dom,
                             virTypedParameterPtr params,
                             int nparams,
                             unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (virTypedParamsValidate(params, nparams,
                               VIR_DOMAIN_BLKIO_WEIGHT,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_BLKIO_DEVICE_WEIGHT,
                               VIR_TYPED_PARAM_STRING,
                               VIR_DOMAIN_BLKIO_DEVICE_READ_IOPS,
                               VIR_TYPED_PARAM_STRING,
                               VIR_DOMAIN_BLKIO_DEVICE_WRITE_IOPS,
                               VIR_TYPED_PARAM_STRING,
                               VIR_DOMAIN_BLKIO_DEVICE_READ_BPS,
                               VIR_TYPED_PARAM_STRING,
                               VIR_DOMAIN_BLKIO_DEVICE_WRITE_BPS,
                               VIR_TYPED_PARAM_STRING,
                               NULL) < 0)
        return -1;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    ret = virDomainDriverSetupPersistentDefBlkioParams(def,
                                                       params,
                                                       nparams);

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetBlkioParameters(virDomainPtr dom,
                             virTypedParameterPtr params,
                             int *nparams,
                             unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    int maxparams = 6;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_TYPED_PARAM_STRING_OKAY, -1);

    if ((*nparams) == 0) {
        *nparams = 6;
        return 0;
    } else if (*nparams < maxparams) {
        maxparams = *nparams;
    }

    *nparams = 0;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (virTypedParameterAssign(&(params[(*nparams)++]),
                                VIR_DOMAIN_BLKIO_WEIGHT,
                                VIR_TYPED_PARAM_UINT,
                                def->blkio.weight) < 0)
        goto cleanup;

    if (virDomainGetBlkioParametersAssignFromDef(def, params, nparams,
                                                 maxparams) < 0)
        goto cleanup;

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

#define TEST_SET_PARAM(index, name, type, value) \
    if (index < *nparams && \
        virTypedParameterAssign(&params[index], name, type, value) < 0) \
        goto cleanup


static int
sfvmDomainSetMemoryParameters(virDomainPtr dom,
                              virTypedParameterPtr params,
                              int nparams,
                              unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    unsigned long long swap_hard_limit = 0;
    unsigned long long hard_limit = 0;
    unsigned long long soft_limit = 0;
    bool set_swap_hard_limit = false;
    bool set_hard_limit = false;
    bool set_soft_limit = false;
    int rc;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (virTypedParamsValidate(params, nparams,
                               VIR_DOMAIN_MEMORY_HARD_LIMIT,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_MEMORY_SOFT_LIMIT,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_MEMORY_SWAP_HARD_LIMIT,
                               VIR_TYPED_PARAM_ULLONG,
                               NULL) < 0)
        return -1;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

#define VIR_GET_LIMIT_PARAMETER(PARAM, VALUE) \
    if ((rc = virTypedParamsGetULLong(params, nparams, PARAM, &VALUE)) < 0) \
        goto cleanup; \
 \
    if (rc == 1) \
        set_ ## VALUE = true;

    VIR_GET_LIMIT_PARAMETER(VIR_DOMAIN_MEMORY_SWAP_HARD_LIMIT, swap_hard_limit)
    VIR_GET_LIMIT_PARAMETER(VIR_DOMAIN_MEMORY_HARD_LIMIT, hard_limit)
    VIR_GET_LIMIT_PARAMETER(VIR_DOMAIN_MEMORY_SOFT_LIMIT, soft_limit)

#undef VIR_GET_LIMIT_PARAMETER

    if (set_swap_hard_limit || set_hard_limit) {
        unsigned long long mem_limit = vm->def->mem.hard_limit;
        unsigned long long swap_limit = vm->def->mem.swap_hard_limit;

        if (set_swap_hard_limit)
            swap_limit = swap_hard_limit;

        if (set_hard_limit)
            mem_limit = hard_limit;

        if (mem_limit > swap_limit) {
            virReportError(VIR_ERR_INVALID_ARG, "%s",
                           _("memory hard_limit tunable value must be lower "
                             "than or equal to swap_hard_limit"));
            goto cleanup;
        }
    }

    if (set_soft_limit)
        def->mem.soft_limit = soft_limit;

    if (set_hard_limit)
        def->mem.hard_limit = hard_limit;

    if (set_swap_hard_limit)
        def->mem.swap_hard_limit = swap_hard_limit;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetMemoryParameters(virDomainPtr dom,
                              virTypedParameterPtr params,
                              int *nparams,
                              unsigned int flags)
{
    int ret = -1;
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_TYPED_PARAM_STRING_OKAY, -1);

    if ((*nparams) == 0) {
        *nparams = 3;
        return 0;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    TEST_SET_PARAM(0, VIR_DOMAIN_MEMORY_HARD_LIMIT, VIR_TYPED_PARAM_ULLONG, def->mem.hard_limit);
    TEST_SET_PARAM(1, VIR_DOMAIN_MEMORY_SOFT_LIMIT, VIR_TYPED_PARAM_ULLONG, def->mem.soft_limit);
    TEST_SET_PARAM(2, VIR_DOMAIN_MEMORY_SWAP_HARD_LIMIT, VIR_TYPED_PARAM_ULLONG, def->mem.swap_hard_limit);

    if (*nparams > 3)
        *nparams = 3;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSetNumaParameters(virDomainPtr dom,
                            virTypedParameterPtr params,
                            int nparams,
                            unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    g_autoptr(virBitmap) nodeset = NULL;
    virDomainNumatuneMemMode config_mode;
    bool live;
    size_t i;
    int mode = -1;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (virTypedParamsValidate(params, nparams,
                               VIR_DOMAIN_NUMA_MODE,
                               VIR_TYPED_PARAM_INT,
                               VIR_DOMAIN_NUMA_NODESET,
                               VIR_TYPED_PARAM_STRING,
                               NULL) < 0)
        return -1;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDefState(vm, flags, &live)))
        goto cleanup;

    for (i = 0; i < nparams; i++) {
        virTypedParameterPtr param = &params[i];

        if (STREQ(param->field, VIR_DOMAIN_NUMA_MODE)) {
            mode = param->value.i;

            if (mode < 0 || mode >= VIR_DOMAIN_NUMATUNE_MEM_LAST) {
                virReportError(VIR_ERR_INVALID_ARG,
                               _("unsupported numatune mode: '%d'"), mode);
                goto cleanup;
            }

        } else if (STREQ(param->field, VIR_DOMAIN_NUMA_NODESET)) {
            if (virBitmapParse(param->value.s, &nodeset,
                               VIR_DOMAIN_CPUMASK_LEN) < 0)
                goto cleanup;

            if (virBitmapIsAllClear(nodeset)) {
                virReportError(VIR_ERR_OPERATION_INVALID,
                               _("Invalid nodeset of 'numatune': %s"),
                               param->value.s);
                goto cleanup;
            }
        }
    }

    if (live &&
        mode != -1 &&
        virDomainNumatuneGetMode(def->numa, -1, &config_mode) == 0 &&
        config_mode != mode) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("can't change numatune mode for running domain"));
        goto cleanup;
    }

    if (virDomainNumatuneSet(def->numa,
                             def->placement_mode ==
                             VIR_DOMAIN_CPU_PLACEMENT_MODE_STATIC,
                             -1, mode, nodeset) < 0)
        goto cleanup;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetNumaParameters(virDomainPtr dom,
                            virTypedParameterPtr params,
                            int *nparams,
                            unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    virDomainNumatuneMemMode mode = VIR_DOMAIN_NUMATUNE_MEM_STRICT;
    g_autofree char *nodeset = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_TYPED_PARAM_STRING_OKAY, -1);

    if ((*nparams) == 0) {
        *nparams = 2;
        return 0;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    ignore_value(virDomainNumatuneGetMode(def->numa, -1, &mode));
    nodeset = virDomainNumatuneFormatNodeset(def->numa, NULL, -1);

    TEST_SET_PARAM(0, VIR_DOMAIN_NUMA_MODE, VIR_TYPED_PARAM_INT, mode);
    TEST_SET_PARAM(1, VIR_DOMAIN_NUMA_NODESET, VIR_TYPED_PARAM_STRING, nodeset);

    nodeset = NULL;

    if (*nparams > 2)
        *nparams = 2;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSetInterfaceParameters(virDomainPtr dom,
                                 const char *device,
                                 virTypedParameterPtr params,
                                 int nparams,
                                 unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def;
    virDomainNetDef *net = NULL;
    g_autoptr(virNetDevBandwidth) bandwidth = NULL;
    bool inboundSpecified = false;
    bool outboundSpecified = false;
    size_t i;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (virTypedParamsValidate(params, nparams,
                               VIR_DOMAIN_BANDWIDTH_IN_AVERAGE,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_BANDWIDTH_IN_PEAK,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_BANDWIDTH_IN_BURST,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_BANDWIDTH_IN_FLOOR,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_BANDWIDTH_OUT_AVERAGE,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_BANDWIDTH_OUT_PEAK,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_BANDWIDTH_OUT_BURST,
                               VIR_TYPED_PARAM_UINT,
                               NULL) < 0)
        return -1;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (!(net = virDomainNetFind(def, device)))
        goto cleanup;

    bandwidth = g_new0(virNetDevBandwidth, 1);
    bandwidth->in = g_new0(virNetDevBandwidthRate, 1);
    bandwidth->out = g_new0(virNetDevBandwidthRate, 1);

    for (i = 0; i < nparams; i++) {
        virTypedParameterPtr param = &params[i];

        if (STREQ(param->field, VIR_DOMAIN_BANDWIDTH_IN_AVERAGE)) {
            bandwidth->in->average = param->value.ui;
            inboundSpecified = true;
        } else if (STREQ(param->field, VIR_DOMAIN_BANDWIDTH_IN_PEAK)) {
            bandwidth->in->peak = param->value.ui;
        } else if (STREQ(param->field, VIR_DOMAIN_BANDWIDTH_IN_BURST)) {
            bandwidth->in->burst = param->value.ui;
        } else if (STREQ(param->field, VIR_DOMAIN_BANDWIDTH_IN_FLOOR)) {
            bandwidth->in->floor = param->value.ui;
            inboundSpecified = true;
        } else if (STREQ(param->field, VIR_DOMAIN_BANDWIDTH_OUT_AVERAGE)) {
            bandwidth->out->average = param->value.ui;
            outboundSpecified = true;
        } else if (STREQ(param->field, VIR_DOMAIN_BANDWIDTH_OUT_PEAK)) {
            bandwidth->out->peak = param->value.ui;
        } else if (STREQ(param->field, VIR_DOMAIN_BANDWIDTH_OUT_BURST)) {
            bandwidth->out->burst = param->value.ui;
        }
    }

    /* average or floor are mandatory, peak and burst are optional */
    if (!bandwidth->in->average && !bandwidth->in->floor)
        VIR_FREE(bandwidth->in);
    if (!bandwidth->out->average)
        VIR_FREE(bandwidth->out);

    if (!net->bandwidth) {
        net->bandwidth = g_steal_pointer(&bandwidth);
    } else {
        if (bandwidth->in) {
            VIR_FREE(net->bandwidth->in);
            net->bandwidth->in = g_steal_pointer(&bandwidth->in);
        } else if (inboundSpecified) {
            /* if we got here it means user requested @inbound to be cleared */
            VIR_FREE(net->bandwidth->in);
        }
        if (bandwidth->out) {
            VIR_FREE(net->bandwidth->out);
            net->bandwidth->out = g_steal_pointer(&bandwidth->out);
        } else if (outboundSpecified) {
            /* if we got here it means user requested @outbound to be cleared */
            VIR_FREE(net->bandwidth->out);
        }
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetInterfaceParameters(virDomainPtr dom,
                                 const char *device,
                                 virTypedParameterPtr params,
                                 int *nparams,
                                 unsigned int flags)
{
    virNetDevBandwidthRate in = {0};
    virNetDevBandwidthRate out = {0};
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    virDomainNetDef *net = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_TYPED_PARAM_STRING_OKAY, -1);

    if ((*nparams) == 0) {
        *nparams = 7;
        return 0;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (!(net = virDomainNetFind(def, device)))
        goto cleanup;

    if (net->bandwidth) {
        if (net->bandwidth->in)
            in = *net->bandwidth->in;
        if (net->bandwidth->out)
            out = *net->bandwidth->out;
    }

    TEST_SET_PARAM(0, VIR_DOMAIN_BANDWIDTH_IN_AVERAGE, VIR_TYPED_PARAM_UINT, in.average);
    TEST_SET_PARAM(1, VIR_DOMAIN_BANDWIDTH_IN_PEAK, VIR_TYPED_PARAM_UINT, in.peak);
    TEST_SET_PARAM(2, VIR_DOMAIN_BANDWIDTH_IN_BURST, VIR_TYPED_PARAM_UINT, in.burst);
    TEST_SET_PARAM(3, VIR_DOMAIN_BANDWIDTH_IN_FLOOR, VIR_TYPED_PARAM_UINT, in.floor);
    TEST_SET_PARAM(4, VIR_DOMAIN_BANDWIDTH_OUT_AVERAGE, VIR_TYPED_PARAM_UINT, out.average);
    TEST_SET_PARAM(5, VIR_DOMAIN_BANDWIDTH_OUT_PEAK, VIR_TYPED_PARAM_UINT, out.peak);
    TEST_SET_PARAM(6, VIR_DOMAIN_BANDWIDTH_OUT_BURST, VIR_TYPED_PARAM_UINT, out.burst);

    if (*nparams > 7)
        *nparams = 7;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


#define TEST_BLOCK_IOTUNE_MAX 1000000000000000LL

static int
sfvmDomainSetBlockIoTune(virDomainPtr dom,
                         const char *path,
                         virTypedParameterPtr params,
                         int nparams,
                         unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    virDomainBlockIoTuneInfo info = {0};
    virDomainDiskDef *conf_disk = NULL;
    virTypedParameterPtr eventParams = NULL;
    int eventNparams = 0;
    int eventMaxparams = 0;
    size_t i;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (virTypedParamsValidate(params, nparams,
                               VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC_MAX,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC_MAX,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC_MAX,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC_MAX,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC_MAX,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC_MAX,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_SIZE_IOPS_SEC,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_GROUP_NAME,
                               VIR_TYPED_PARAM_STRING,
                               VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC_MAX_LENGTH,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC_MAX_LENGTH,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC_MAX_LENGTH,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC_MAX_LENGTH,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC_MAX_LENGTH,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC_MAX_LENGTH,
                               VIR_TYPED_PARAM_ULLONG,
                               NULL) < 0)
        return -1;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (!(conf_disk = virDomainDiskByName(def, path, true))) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("missing persistent configuration for disk '%s'"),
                       path);
        goto cleanup;
    }

    info = conf_disk->blkdeviotune;
    info.group_name = g_strdup(conf_disk->blkdeviotune.group_name);

    if (virTypedParamsAddString(&eventParams, &eventNparams, &eventMaxparams,
                                VIR_DOMAIN_TUNABLE_BLKDEV_DISK, path) < 0)
        goto cleanup;

#define SET_IOTUNE_FIELD(FIELD, STR, TUNABLE_STR) \
    if (STREQ(param->field, STR)) { \
        info.FIELD = param->value.ul; \
        if (virTypedParamsAddULLong(&eventParams, &eventNparams, \
                                    &eventMaxparams, \
                                    TUNABLE_STR, \
                                    param->value.ul) < 0) \
            goto cleanup; \
        continue; \
    }

    for (i = 0; i < nparams; i++) {
        virTypedParameterPtr param = &params[i];

        if (param->value.ul > TEST_BLOCK_IOTUNE_MAX) {
            virReportError(VIR_ERR_ARGUMENT_UNSUPPORTED,
                           _("block I/O throttle limit value must"
                             " be no more than %llu"), TEST_BLOCK_IOTUNE_MAX);
            goto cleanup;
        }

        SET_IOTUNE_FIELD(total_bytes_sec,
                         VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC,
                         VIR_DOMAIN_TUNABLE_BLKDEV_TOTAL_BYTES_SEC);
        SET_IOTUNE_FIELD(read_bytes_sec,
                         VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC,
                         VIR_DOMAIN_TUNABLE_BLKDEV_READ_BYTES_SEC);
        SET_IOTUNE_FIELD(write_bytes_sec,
                         VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC,
                         VIR_DOMAIN_TUNABLE_BLKDEV_WRITE_BYTES_SEC);
        SET_IOTUNE_FIELD(total_iops_sec,
                         VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC,
                         VIR_DOMAIN_TUNABLE_BLKDEV_TOTAL_IOPS_SEC);
        SET_IOTUNE_FIELD(read_iops_sec,
                         VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC,
                         VIR_DOMAIN_TUNABLE_BLKDEV_READ_IOPS_SEC);
        SET_IOTUNE_FIELD(write_iops_sec,
                         VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC,
                         VIR_DOMAIN_TUNABLE_BLKDEV_WRITE_IOPS_SEC);

        SET_IOTUNE_FIELD(total_bytes_sec_max,
                         VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC_MAX,
                         VIR_DOMAIN_TUNABLE_BLKDEV_TOTAL_BYTES_SEC_MAX);
        SET_IOTUNE_FIELD(read_bytes_sec_max,
                         VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC_MAX,
                         VIR_DOMAIN_TUNABLE_BLKDEV_READ_BYTES_SEC_MAX);
        SET_IOTUNE_FIELD(write_bytes_sec_max,
                         VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC_MAX,
                         VIR_DOMAIN_TUNABLE_BLKDEV_WRITE_BYTES_SEC_MAX);
        SET_IOTUNE_FIELD(total_iops_sec_max,
                         VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC_MAX,
                         VIR_DOMAIN_TUNABLE_BLKDEV_TOTAL_IOPS_SEC_MAX);
        SET_IOTUNE_FIELD(read_iops_sec_max,
                         VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC_MAX,
                         VIR_DOMAIN_TUNABLE_BLKDEV_READ_IOPS_SEC_MAX);
        SET_IOTUNE_FIELD(write_iops_sec_max,
                         VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC_MAX,
                         VIR_DOMAIN_TUNABLE_BLKDEV_WRITE_IOPS_SEC_MAX);
        SET_IOTUNE_FIELD(size_iops_sec,
                         VIR_DOMAIN_BLOCK_IOTUNE_SIZE_IOPS_SEC,
                         VIR_DOMAIN_TUNABLE_BLKDEV_SIZE_IOPS_SEC);

        if (STREQ(param->field, VIR_DOMAIN_BLOCK_IOTUNE_GROUP_NAME)) {
            VIR_FREE(info.group_name);
            info.group_name = g_strdup(param->value.s);
            if (virTypedParamsAddString(&eventParams,
                                        &eventNparams,
                                        &eventMaxparams,
                                        VIR_DOMAIN_TUNABLE_BLKDEV_GROUP_NAME,
                                        param->value.s) < 0)
                goto cleanup;
            continue;
        }

        SET_IOTUNE_FIELD(total_bytes_sec_max_length,
                         VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC_MAX_LENGTH,
                         VIR_DOMAIN_TUNABLE_BLKDEV_TOTAL_BYTES_SEC_MAX_LENGTH);
        SET_IOTUNE_FIELD(read_bytes_sec_max_length,
                         VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC_MAX_LENGTH,
                         VIR_DOMAIN_TUNABLE_BLKDEV_READ_BYTES_SEC_MAX_LENGTH);
        SET_IOTUNE_FIELD(write_bytes_sec_max_length,
                         VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC_MAX_LENGTH,
                         VIR_DOMAIN_TUNABLE_BLKDEV_WRITE_BYTES_SEC_MAX_LENGTH);
        SET_IOTUNE_FIELD(total_iops_sec_max_length,
                         VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC_MAX_LENGTH,
                         VIR_DOMAIN_TUNABLE_BLKDEV_TOTAL_IOPS_SEC_MAX_LENGTH);
        SET_IOTUNE_FIELD(read_iops_sec_max_length,
                         VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC_MAX_LENGTH,
                         VIR_DOMAIN_TUNABLE_BLKDEV_READ_IOPS_SEC_MAX_LENGTH);
        SET_IOTUNE_FIELD(write_iops_sec_max_length,
                         VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC_MAX_LENGTH,
                         VIR_DOMAIN_TUNABLE_BLKDEV_WRITE_IOPS_SEC_MAX_LENGTH);
    }
#undef SET_IOTUNE_FIELD

    if ((info.total_bytes_sec && info.read_bytes_sec) ||
        (info.total_bytes_sec && info.write_bytes_sec)) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("total and read/write of bytes_sec "
                         "cannot be set at the same time"));
        goto cleanup;
    }

    if ((info.total_iops_sec && info.read_iops_sec) ||
        (info.total_iops_sec && info.write_iops_sec)) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("total and read/write of iops_sec "
                         "cannot be set at the same time"));
        goto cleanup;
    }

    if ((info.total_bytes_sec_max && info.read_bytes_sec_max) ||
        (info.total_bytes_sec_max && info.write_bytes_sec_max)) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("total and read/write of bytes_sec_max "
                         "cannot be set at the same time"));
        goto cleanup;
    }

    if ((info.total_iops_sec_max && info.read_iops_sec_max) ||
        (info.total_iops_sec_max && info.write_iops_sec_max)) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("total and read/write of iops_sec_max "
                         "cannot be set at the same time"));
        goto cleanup;
    }


#define TEST_BLOCK_IOTUNE_MAX_CHECK(FIELD, FIELD_MAX) \
    do { \
        if (info.FIELD > info.FIELD_MAX) { \
            virReportError(VIR_ERR_INVALID_ARG, \
                           _("%s cannot be set higher than %s "), \
                             #FIELD, #FIELD_MAX); \
            goto cleanup; \
        } \
    } while (0);

    TEST_BLOCK_IOTUNE_MAX_CHECK(total_bytes_sec, total_bytes_sec_max);
    TEST_BLOCK_IOTUNE_MAX_CHECK(read_bytes_sec, read_bytes_sec_max);
    TEST_BLOCK_IOTUNE_MAX_CHECK(write_bytes_sec, write_bytes_sec_max);
    TEST_BLOCK_IOTUNE_MAX_CHECK(total_iops_sec, total_iops_sec_max);
    TEST_BLOCK_IOTUNE_MAX_CHECK(read_iops_sec, read_iops_sec_max);
    TEST_BLOCK_IOTUNE_MAX_CHECK(write_iops_sec, write_iops_sec_max);

#undef TEST_BLOCK_IOTUNE_MAX_CHECK

    virDomainDiskSetBlockIOTune(conf_disk, &info);

    ret = 0;
 cleanup:
    VIR_FREE(info.group_name);
    virDomainObjEndAPI(&vm);
    if (eventNparams)
        virTypedParamsFree(eventParams, eventNparams);
    return ret;
}


static int
sfvmDomainGetBlockIoTune(virDomainPtr dom,
                         const char *path,
                         virTypedParameterPtr params,
                         int *nparams,
                         unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    virDomainDiskDef *disk;
    virDomainBlockIoTuneInfo reply = {0};
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_TYPED_PARAM_STRING_OKAY, -1);

    flags &= ~VIR_TYPED_PARAM_STRING_OKAY;

    if (*nparams == 0) {
        *nparams = 20;
        return 0;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (!(disk = virDomainDiskByName(def, path, true))) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("disk '%s' was not found in the domain config"),
                       path);
        goto cleanup;
    }

    reply = disk->blkdeviotune;
    reply.group_name = g_strdup(disk->blkdeviotune.group_name);

    TEST_SET_PARAM(0, VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC,
                   VIR_TYPED_PARAM_ULLONG, reply.total_bytes_sec);
    TEST_SET_PARAM(1, VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC,
                   VIR_TYPED_PARAM_ULLONG, reply.read_bytes_sec);
    TEST_SET_PARAM(2, VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC,
                   VIR_TYPED_PARAM_ULLONG, reply.write_bytes_sec);

    TEST_SET_PARAM(3, VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC,
                   VIR_TYPED_PARAM_ULLONG, reply.total_iops_sec);
    TEST_SET_PARAM(4, VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC,
                   VIR_TYPED_PARAM_ULLONG, reply.read_iops_sec);
    TEST_SET_PARAM(5, VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC,
                   VIR_TYPED_PARAM_ULLONG, reply.write_iops_sec);

    TEST_SET_PARAM(6, VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC_MAX,
                   VIR_TYPED_PARAM_ULLONG, reply.total_bytes_sec_max);
    TEST_SET_PARAM(7, VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC_MAX,
                   VIR_TYPED_PARAM_ULLONG, reply.read_bytes_sec_max);
    TEST_SET_PARAM(8, VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC_MAX,
                   VIR_TYPED_PARAM_ULLONG, reply.write_bytes_sec_max);

    TEST_SET_PARAM(9, VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC_MAX,
                   VIR_TYPED_PARAM_ULLONG, reply.total_iops_sec_max);
    TEST_SET_PARAM(10, VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC_MAX,
                   VIR_TYPED_PARAM_ULLONG, reply.read_iops_sec_max);
    TEST_SET_PARAM(11, VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC_MAX,
                   VIR_TYPED_PARAM_ULLONG, reply.write_iops_sec_max);

    TEST_SET_PARAM(12, VIR_DOMAIN_BLOCK_IOTUNE_SIZE_IOPS_SEC,
                   VIR_TYPED_PARAM_ULLONG, reply.size_iops_sec);

    TEST_SET_PARAM(13, VIR_DOMAIN_BLOCK_IOTUNE_GROUP_NAME,
                   VIR_TYPED_PARAM_STRING, reply.group_name);
    reply.group_name = NULL;

    TEST_SET_PARAM(14, VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_BYTES_SEC_MAX_LENGTH,
                   VIR_TYPED_PARAM_ULLONG, reply.total_bytes_sec_max_length);
    TEST_SET_PARAM(15, VIR_DOMAIN_BLOCK_IOTUNE_READ_BYTES_SEC_MAX_LENGTH,
                   VIR_TYPED_PARAM_ULLONG, reply.read_bytes_sec_max_length);
    TEST_SET_PARAM(16, VIR_DOMAIN_BLOCK_IOTUNE_WRITE_BYTES_SEC_MAX_LENGTH,
                   VIR_TYPED_PARAM_ULLONG, reply.write_bytes_sec_max_length);

    TEST_SET_PARAM(17, VIR_DOMAIN_BLOCK_IOTUNE_TOTAL_IOPS_SEC_MAX_LENGTH,
                   VIR_TYPED_PARAM_ULLONG, reply.total_iops_sec_max_length);
    TEST_SET_PARAM(18, VIR_DOMAIN_BLOCK_IOTUNE_READ_IOPS_SEC_MAX_LENGTH,
                   VIR_TYPED_PARAM_ULLONG, reply.read_iops_sec_max_length);
    TEST_SET_PARAM(19, VIR_DOMAIN_BLOCK_IOTUNE_WRITE_IOPS_SEC_MAX_LENGTH,
                   VIR_TYPED_PARAM_ULLONG, reply.write_iops_sec_max_length);

    if (*nparams > 20)
        *nparams = 20;

    ret = 0;
 cleanup:
    VIR_FREE(reply.group_name);
    virDomainObjEndAPI(&vm);
    return ret;
}
#undef TEST_SET_PARAM


static int sfvmConnectNumOfDefinedDomains(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;

    return virDomainObjListNumOfDomains(privconn->domains, false, NULL, NULL);
}

static int sfvmConnectListDefinedDomains(virConnectPtr conn,
                                         char **const names,
                                         int maxnames)
{
    sfvmDriver *privconn = conn->privateData;

    memset(names, 0, sizeof(*names)*maxnames);
    return virDomainObjListGetInactiveNames(privconn->domains, names, maxnames,
                                            NULL, NULL);
}

static virDomainPtr sfvmDomainDefineXMLFlags(virConnectPtr conn,
                                             const char *xml,
                                             unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    virDomainPtr ret = NULL;
    g_autoptr(virDomainDef) def = NULL;
    virDomainObj *dom = NULL;
    virObjectEvent *event = NULL;
    g_autoptr(virDomainDef) oldDef = NULL;
    unsigned int parse_flags = VIR_DOMAIN_DEF_PARSE_INACTIVE;

    virCheckFlags(VIR_DOMAIN_DEFINE_VALIDATE, NULL);

    if (flags & VIR_DOMAIN_DEFINE_VALIDATE)
        parse_flags |= VIR_DOMAIN_DEF_PARSE_VALIDATE_SCHEMA;

    if ((def = virDomainDefParseString(xml, privconn->xmlopt,
                                       NULL, parse_flags)) == NULL)
        goto cleanup;

    if (virXMLCheckIllegalChars("name", def->name, "\n") < 0)
        goto cleanup;

    if (sfvmDomainGenerateIfnames(def) < 0)
        goto cleanup;
    if (!(dom = virDomainObjListAdd(privconn->domains,
                                    &def,
                                    privconn->xmlopt,
                                    0,
                                    &oldDef)))
        goto cleanup;
    dom->persistent = 1;

    event = virDomainEventLifecycleNewFromObj(dom,
                                     VIR_DOMAIN_EVENT_DEFINED,
                                     !oldDef ?
                                     VIR_DOMAIN_EVENT_DEFINED_ADDED :
                                     VIR_DOMAIN_EVENT_DEFINED_UPDATED);

    ret = virGetDomain(conn, dom->def->name, dom->def->uuid, dom->def->id);

 cleanup:
    virDomainObjEndAPI(&dom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}

static virDomainPtr
sfvmDomainDefineXML(virConnectPtr conn, const char *xml)
{
    return sfvmDomainDefineXMLFlags(conn, xml, 0);
}

static char *sfvmDomainGetMetadata(virDomainPtr dom,
                                   int type,
                                   const char *uri,
                                   unsigned int flags)
{
    virDomainObj *privdom;
    char *ret;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, NULL);

    if (!(privdom = sfvmDomObjFromDomain(dom)))
        return NULL;

    ret = virDomainObjGetMetadata(privdom, type, uri, flags);

    virDomainObjEndAPI(&privdom);
    return ret;
}

static int sfvmDomainSetMetadata(virDomainPtr dom,
                                 int type,
                                 const char *metadata,
                                 const char *key,
                                 const char *uri,
                                 unsigned int flags)
{
    sfvmDriver *privconn = dom->conn->privateData;
    virDomainObj *privdom;
    int ret;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (!(privdom = sfvmDomObjFromDomain(dom)))
        return -1;

    ret = virDomainObjSetMetadata(privdom, type, metadata, key, uri,
                                  privconn->xmlopt,
                                  NULL, NULL, flags);

    if (ret == 0) {
        virObjectEvent *ev = NULL;
        ev = virDomainEventMetadataChangeNewFromObj(privdom, type, uri);
        virObjectEventStateQueue(privconn->eventState, ev);
    }

    virDomainObjEndAPI(&privdom);
    return ret;
}

#define TEST_TOTAL_CPUTIME 48772617035LL

static int
sfvmDomainGetDomainTotalCpuStats(virTypedParameterPtr params,
                                 int nparams)
{
    if (nparams == 0) /* return supported number of params */
        return 3;

    if (virTypedParameterAssign(&params[0], VIR_DOMAIN_CPU_STATS_CPUTIME,
                                VIR_TYPED_PARAM_ULLONG, TEST_TOTAL_CPUTIME) < 0)
        return -1;

    if (nparams > 1 &&
        virTypedParameterAssign(&params[1],
                                VIR_DOMAIN_CPU_STATS_USERTIME,
                                VIR_TYPED_PARAM_ULLONG, 5540000000) < 0)
        return -1;

    if (nparams > 2 &&
        virTypedParameterAssign(&params[2],
                                VIR_DOMAIN_CPU_STATS_SYSTEMTIME,
                                VIR_TYPED_PARAM_ULLONG, 6460000000) < 0)
        return -1;

    if (nparams > 3)
        nparams = 3;

    return nparams;
}


static int
sfvmDomainGetPercpuStats(virTypedParameterPtr params,
                         unsigned int nparams,
                         int start_cpu,
                         unsigned int ncpus,
                         int total_cpus)
{
    size_t i;
    int need_cpus;
    int param_idx;
    unsigned long long percpu_time = (TEST_TOTAL_CPUTIME / total_cpus);

    /* return the number of supported params */
    if (nparams == 0 && ncpus != 0)
        return 2;

    /* return total number of cpus */
    if (ncpus == 0)
        return total_cpus;

    if (start_cpu >= total_cpus) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("start_cpu %d larger than maximum of %d"),
                       start_cpu, total_cpus - 1);
        return -1;
    }

    /* return percpu cputime in index 0 */
    param_idx = 0;

    /* number of cpus to compute */
    need_cpus = MIN(total_cpus, start_cpu + ncpus);

    for (i = start_cpu; i < need_cpus; i++) {
        int idx = (i - start_cpu) * nparams + param_idx;

        if (virTypedParameterAssign(&params[idx],
                                    VIR_DOMAIN_CPU_STATS_CPUTIME,
                                    VIR_TYPED_PARAM_ULLONG,
                                    percpu_time + i) < 0)
            return -1;
    }

    /* return percpu vcputime in index 1 */
    param_idx = 1;

    if (param_idx < nparams) {
        for (i = start_cpu; i < need_cpus; i++) {
            int idx = (i - start_cpu) * nparams + param_idx;

            if (virTypedParameterAssign(&params[idx],
                                        VIR_DOMAIN_CPU_STATS_VCPUTIME,
                                        VIR_TYPED_PARAM_ULLONG,
                                        percpu_time + i - 1234567890) < 0)
                return -1;
        }
        param_idx++;
    }

    return param_idx;
}


static int
sfvmDomainGetCPUStats(virDomainPtr dom,
                      virTypedParameterPtr params,
                      unsigned int nparams,
                      int start_cpu,
                      unsigned int ncpus,
                      unsigned int flags)
{
    virDomainObj *vm = NULL;
    sfvmDriver *privconn = dom->conn->privateData;
    int ret = -1;

    virCheckFlags(VIR_TYPED_PARAM_STRING_OKAY, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    if (start_cpu == -1)
        ret = sfvmDomainGetDomainTotalCpuStats(params, nparams);
    else
        ret = sfvmDomainGetPercpuStats(params, nparams, start_cpu, ncpus,
                                       privconn->nodeInfo.cores);

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSendProcessSignal(virDomainPtr dom,
                            long long pid_value,
                            unsigned int signum,
                            unsigned int flags)
{
    int ret = -1;
    virDomainObj *vm = NULL;

    virCheckFlags(0, -1);

    if (pid_value != 1) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("only sending a signal to pid 1 is supported"));
        return -1;
    }

    if (signum >= VIR_DOMAIN_PROCESS_SIGNAL_LAST) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("signum value %d is out of range"),
                       signum);
        return -1;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    /* do nothing */
    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int sfvmNodeGetCellsFreeMemory(virConnectPtr conn,
                                      unsigned long long *freemems,
                                      int startCell, int maxCells)
{
    sfvmDriver *privconn = conn->privateData;
    int cell;
    size_t i;
    int ret = -1;

    virObjectLock(privconn);
    if (startCell >= privconn->numCells) {
        virReportError(VIR_ERR_INVALID_ARG,
                       "%s", _("Range exceeds available cells"));
        goto cleanup;
    }

    for (cell = startCell, i = 0;
         (cell < privconn->numCells && i < maxCells);
         ++cell, ++i) {
        freemems[i] = privconn->cells[cell].mem;
    }
    ret = i;

 cleanup:
    virObjectUnlock(privconn);
    return ret;
}

#define TEST_NB_CPU_STATS 4

static int
sfvmNodeGetCPUStats(virConnectPtr conn G_GNUC_UNUSED,
                    int cpuNum G_GNUC_UNUSED,
                    virNodeCPUStatsPtr params,
                    int *nparams,
                    unsigned int flags)
{
    size_t i = 0;

    virCheckFlags(0, -1);

    if (params == NULL) {
        *nparams = TEST_NB_CPU_STATS;
        return 0;
    }

    for (i = 0; i < *nparams && i < 4; i++) {
        switch (i) {
        case 0:
            if (virHostCPUStatsAssign(&params[i],
                                      VIR_NODE_CPU_STATS_USER, 9797400000) < 0)
                return -1;
            break;
        case 1:
            if (virHostCPUStatsAssign(&params[i],
                                      VIR_NODE_CPU_STATS_KERNEL, 34678723400000) < 0)
                return -1;
            break;
        case 2:
            if (virHostCPUStatsAssign(&params[i],
                                      VIR_NODE_CPU_STATS_IDLE, 87264900000) < 0)
                return -1;
            break;
        case 3:
            if (virHostCPUStatsAssign(&params[i],
                                      VIR_NODE_CPU_STATS_IOWAIT, 763600000) < 0)
                return -1;
            break;
        }
    }

    *nparams = i;
    return 0;
}

static unsigned long long
sfvmNodeGetFreeMemory(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    unsigned int freeMem = 0;
    size_t i;

    virObjectLock(privconn);

    for (i = 0; i < privconn->numCells; i++)
        freeMem += privconn->cells[i].freeMem;

    virObjectUnlock(privconn);
    return freeMem;
}

static int
sfvmNodeGetFreePages(virConnectPtr conn G_GNUC_UNUSED,
                     unsigned int npages,
                     unsigned int *pages G_GNUC_UNUSED,
                     int startCell G_GNUC_UNUSED,
                     unsigned int cellCount,
                     unsigned long long *counts,
                     unsigned int flags)
{
    size_t i = 0, j = 0;
    int x = 6;

    virCheckFlags(0, -1);

    for (i = 0; i < cellCount; i++) {
        for (j = 0; j < npages; j++) {
            x = x * 2 + 7;
            counts[(i * npages) +  j] = x;
        }
    }

    return 0;
}

static int sfvmDomainCreateWithFlags(virDomainPtr domain, unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(0, -1);

    virObjectLock(privconn);

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjGetState(privdom, NULL) != VIR_DOMAIN_SHUTOFF) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("Domain '%s' is already running"), domain->name);
        goto cleanup;
    }

    if (sfvmDomainStartState(privconn, privdom,
                             VIR_DOMAIN_RUNNING_BOOTED) < 0)
        goto cleanup;
    domain->id = privdom->def->id;

    event = virDomainEventLifecycleNewFromObj(privdom,
                                     VIR_DOMAIN_EVENT_STARTED,
                                     VIR_DOMAIN_EVENT_STARTED_BOOTED);
    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    virObjectUnlock(privconn);
    return ret;
}

static int sfvmDomainCreate(virDomainPtr domain)
{
    return sfvmDomainCreateWithFlags(domain, 0);
}


static int sfvmDomainCreateWithFiles(virDomainPtr domain,
                                     unsigned int nfiles G_GNUC_UNUSED,
                                     int *files G_GNUC_UNUSED,
                                     unsigned int flags)
{
    return sfvmDomainCreateWithFlags(domain, flags);
}


static int sfvmDomainUndefineFlags(virDomainPtr domain,
                                   unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *privdom;
    virObjectEvent *event = NULL;
    int nsnapshots;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_UNDEFINE_MANAGED_SAVE |
                  VIR_DOMAIN_UNDEFINE_SNAPSHOTS_METADATA, -1);


    if (!(privdom = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (privdom->hasManagedSave &&
        !(flags & VIR_DOMAIN_UNDEFINE_MANAGED_SAVE)) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("Refusing to undefine while domain managed "
                         "save image exists"));
        goto cleanup;
    }

    /* Requiring an inactive VM is part of the documented API for
     * UNDEFINE_SNAPSHOTS_METADATA
     */
    if (!virDomainObjIsActive(privdom) &&
        (nsnapshots = virDomainSnapshotObjListNum(privdom->snapshots,
                                                  NULL, 0))) {
        if (!(flags & VIR_DOMAIN_UNDEFINE_SNAPSHOTS_METADATA)) {
            virReportError(VIR_ERR_OPERATION_INVALID,
                           _("cannot delete inactive domain with %d "
                             "snapshots"),
                           nsnapshots);
            goto cleanup;
        }

        /* There isn't actually anything to do, we are just emulating qemu
         * behavior here. */
    }

    event = virDomainEventLifecycleNewFromObj(privdom,
                                     VIR_DOMAIN_EVENT_UNDEFINED,
                                     VIR_DOMAIN_EVENT_UNDEFINED_REMOVED);
    privdom->hasManagedSave = false;

    if (virDomainObjIsActive(privdom))
        privdom->persistent = 0;
    else
        virDomainObjListRemove(privconn->domains, privdom);

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    virObjectEventStateQueue(privconn->eventState, event);
    return ret;
}

static int sfvmDomainUndefine(virDomainPtr domain)
{
    return sfvmDomainUndefineFlags(domain, 0);
}


static int
sfvmDomainFSFreeze(virDomainPtr dom,
                   const char **mountpoints,
                   unsigned int nmountpoints,
                   unsigned int flags)
{
    virDomainObj *vm;
    sfvmDomainObjPrivate *priv;
    size_t i;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    priv = vm->privateData;

    if (nmountpoints == 0) {
        ret = 2 - (priv->frozen[0] + priv->frozen[1]);
        priv->frozen[0] = priv->frozen[1] = true;
    } else {
        int nfreeze = 0;
        bool freeze[2];

        memcpy(&freeze, priv->frozen, 2);

        for (i = 0; i < nmountpoints; i++) {
            if (STREQ(mountpoints[i], "/")) {
                if (!freeze[0]) {
                    freeze[0] = true;
                    nfreeze++;
                }
            } else if (STREQ(mountpoints[i], "/boot")) {
                if (!freeze[1]) {
                    freeze[1] = true;
                    nfreeze++;
                }
            } else {
                virReportError(VIR_ERR_OPERATION_INVALID,
                               _("mount point not found: %s"),
                               mountpoints[i]);
                goto cleanup;
            }
        }

        /* steal the helper copy */
        memcpy(priv->frozen, &freeze, 2);
        ret = nfreeze;
    }

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainFSThaw(virDomainPtr dom,
                   const char **mountpoints,
                   unsigned int nmountpoints,
                   unsigned int flags)
{
    virDomainObj *vm;
    sfvmDomainObjPrivate *priv;
    size_t i;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    priv = vm->privateData;

    if (nmountpoints == 0) {
        ret = priv->frozen[0] + priv->frozen[1];
        priv->frozen[0] = priv->frozen[1] = false;
    } else {
        int nthaw = 0;
        bool freeze[2];

        memcpy(&freeze, priv->frozen, 2);

        for (i = 0; i < nmountpoints; i++) {
            if (STREQ(mountpoints[i], "/")) {
                if (freeze[0]) {
                    freeze[0] = false;
                    nthaw++;
                }
            } else if (STREQ(mountpoints[i], "/boot")) {
                if (freeze[1]) {
                    freeze[1] = false;
                    nthaw++;
                }
            } else {
                virReportError(VIR_ERR_OPERATION_INVALID,
                               _("mount point not found: %s"),
                               mountpoints[i]);
                goto cleanup;
            }
        }

        /* steal the helper copy */
        memcpy(priv->frozen, &freeze, 2);
        ret = nthaw;
    }

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainFSTrim(virDomainPtr dom,
                 const char *mountPoint,
                 unsigned long long minimum G_GNUC_UNUSED,
                 unsigned int flags)
{
    virDomainObj *vm;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    if (mountPoint && STRNEQ(mountPoint, "/") && STRNEQ(mountPoint, "/boot")) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       _("mount point not found: %s"),
                       mountPoint);
        goto cleanup;
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int sfvmDomainGetAutostart(virDomainPtr domain,
                                  int *autostart)
{
    virDomainObj *privdom;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    *autostart = privdom->autostart;

    virDomainObjEndAPI(&privdom);
    return 0;
}


static int sfvmDomainSetAutostart(virDomainPtr domain,
                                  int autostart)
{
    virDomainObj *privdom;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    privdom->autostart = autostart ? 1 : 0;

    virDomainObjEndAPI(&privdom);
    return 0;
}

static int sfvmDomainGetDiskErrors(virDomainPtr dom,
                                   virDomainDiskErrorPtr errors,
                                   unsigned int maxerrors,
                                   unsigned int flags)
{
    virDomainObj *vm = NULL;
    int ret = -1;
    size_t i;
    size_t nerrors = 0;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    nerrors = MIN(vm->def->ndisks, maxerrors);

    if (errors) {
        /* sanitize input */
        memset(errors, 0, sizeof(virDomainDiskError) * nerrors);

        for (i = 0; i < nerrors; i++) {
            errors[i].disk = g_strdup(vm->def->disks[i]->dst);
            errors[i].error = (i % (VIR_DOMAIN_DISK_ERROR_LAST - 1)) + 1;
        }
        ret = i;
    } else {
        ret = vm->def->ndisks;
    }

 cleanup:
    if (ret < 0) {
        for (i = 0; i < nerrors; i++)
            VIR_FREE(errors[i].disk);
    }
    virDomainObjEndAPI(&vm);
    return ret;
}



static int
sfvmDomainGetFSInfo(virDomainPtr dom,
                    virDomainFSInfoPtr **info,
                    unsigned int flags)
{
    size_t i;
    virDomainObj *vm;
    virDomainFSInfoPtr *info_ret = NULL;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    *info = NULL;

    for (i = 0; i < vm->def->ndisks; i++) {
        if (vm->def->disks[i]->device == VIR_DOMAIN_DISK_DEVICE_DISK) {
            char *name = vm->def->disks[i]->dst;

            info_ret = g_new0(virDomainFSInfo *, 2);
            info_ret[0] = g_new0(virDomainFSInfo, 1);
            info_ret[0]->devAlias = g_new0(char *, 1);

            info_ret[0]->mountpoint = g_strdup("/");
            info_ret[0]->fstype = g_strdup("ext4");
            info_ret[0]->devAlias[0] = g_strdup(name);
            info_ret[0]->name = g_strdup_printf("%s1", name);

            info_ret[1] = g_new0(virDomainFSInfo, 1);
            info_ret[1]->devAlias = g_new0(char *, 1);

            info_ret[1]->mountpoint = g_strdup("/boot");
            info_ret[1]->fstype = g_strdup("ext4");
            info_ret[1]->devAlias[0] = g_strdup(name);
            info_ret[1]->name = g_strdup_printf("%s2", name);

            info_ret[0]->ndevAlias = info_ret[1]->ndevAlias = 1;

            *info = g_steal_pointer(&info_ret);

            ret = 2;
            goto cleanup;
        }
    }

    ret = 0;

 cleanup:
    if (info_ret) {
        virDomainFSInfoFree(info_ret[0]);
        virDomainFSInfoFree(info_ret[1]);
        VIR_FREE(info_ret);
    }

    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSetPerfEvents(virDomainPtr dom,
                        virTypedParameterPtr params,
                        int nparams,
                        unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    size_t i;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (virTypedParamsValidate(params, nparams,
                               VIR_PERF_PARAM_CMT, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_MBMT, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_MBML, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_CPU_CYCLES, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_INSTRUCTIONS, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_CACHE_REFERENCES, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_CACHE_MISSES, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_BRANCH_INSTRUCTIONS, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_BRANCH_MISSES, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_BUS_CYCLES, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_STALLED_CYCLES_FRONTEND, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_STALLED_CYCLES_BACKEND, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_REF_CPU_CYCLES, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_CPU_CLOCK, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_TASK_CLOCK, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_PAGE_FAULTS, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_CONTEXT_SWITCHES, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_CPU_MIGRATIONS, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_PAGE_FAULTS_MIN, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_PAGE_FAULTS_MAJ, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_ALIGNMENT_FAULTS, VIR_TYPED_PARAM_BOOLEAN,
                               VIR_PERF_PARAM_EMULATION_FAULTS, VIR_TYPED_PARAM_BOOLEAN,
                               NULL) < 0)
        return -1;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    for (i = 0; i < nparams; i++) {
        virTypedParameterPtr param = &params[i];
        virPerfEventType type = virPerfEventTypeFromString(param->field);

        if (param->value.b)
            def->perf.events[type] = VIR_TRISTATE_BOOL_YES;
        else
            def->perf.events[type] = VIR_TRISTATE_BOOL_NO;
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetPerfEvents(virDomainPtr dom,
                        virTypedParameterPtr *params,
                        int *nparams,
                        unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    virTypedParameterPtr par = NULL;
    size_t i;
    int maxpar = 0;
    int npar = 0;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG |
                  VIR_TYPED_PARAM_STRING_OKAY, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    for (i = 0; i < VIR_PERF_EVENT_LAST; i++) {
        if (virTypedParamsAddBoolean(&par, &npar, &maxpar,
                                     virPerfEventTypeToString(i),
                                     def->perf.events[i] == VIR_TRISTATE_BOOL_YES) < 0)
            goto cleanup;
    }

    *params = g_steal_pointer(&par);
    *nparams = npar;
    npar = 0;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    virTypedParamsFree(par, npar);
    return ret;
}


static char *sfvmDomainGetSchedulerType(virDomainPtr domain G_GNUC_UNUSED,
                                        int *nparams)
{
    if (nparams)
        *nparams = 1;

    return g_strdup("fair");
}

static int
sfvmDomainGetSchedulerParametersFlags(virDomainPtr domain,
                                      virTypedParameterPtr params,
                                      int *nparams,
                                      unsigned int flags)
{
    virDomainObj *privdom;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    if (virTypedParameterAssign(params, VIR_DOMAIN_SCHEDULER_WEIGHT,
                                VIR_TYPED_PARAM_UINT, 50) < 0)
        goto cleanup;
    /* XXX */
    /*params[0].value.ui = privdom->weight;*/

    *nparams = 1;
    ret = 0;

 cleanup:
    virDomainObjEndAPI(&privdom);
    return ret;
}

static int
sfvmDomainGetSchedulerParameters(virDomainPtr domain,
                                 virTypedParameterPtr params,
                                 int *nparams)
{
    return sfvmDomainGetSchedulerParametersFlags(domain, params, nparams, 0);
}

static int
sfvmDomainSetSchedulerParametersFlags(virDomainPtr domain,
                                      virTypedParameterPtr params,
                                      int nparams,
                                      unsigned int flags)
{
    virDomainObj *privdom;
    int ret = -1;
    size_t i;

    virCheckFlags(0, -1);
    if (virTypedParamsValidate(params, nparams,
                               VIR_DOMAIN_SCHEDULER_WEIGHT,
                               VIR_TYPED_PARAM_UINT,
                               NULL) < 0)
        return -1;

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    for (i = 0; i < nparams; i++) {
        if (STREQ(params[i].field, VIR_DOMAIN_SCHEDULER_WEIGHT)) {
            /* XXX */
            /*privdom->weight = params[i].value.ui;*/
        }
    }

    ret = 0;

    virDomainObjEndAPI(&privdom);
    return ret;
}

static int
sfvmDomainSetSchedulerParameters(virDomainPtr domain,
                                 virTypedParameterPtr params,
                                 int nparams)
{
    return sfvmDomainSetSchedulerParametersFlags(domain, params, nparams, 0);
}

static int sfvmDomainBlockStats(virDomainPtr domain,
                                const char *path,
                                virDomainBlockStatsPtr stats)
{
    virDomainObj *privdom;
    unsigned long long statbase;
    int ret = -1;

    if (!*path) {
        virReportError(VIR_ERR_OPERATION_UNSUPPORTED, "%s",
                       _("summary statistics are not supported yet"));
        return ret;
    }

    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return ret;

    if (virDomainObjCheckActive(privdom) < 0)
        goto error;

    if (virDomainDiskIndexByName(privdom->def, path, false) < 0) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("invalid path: %s"), path);
        goto error;
    }

    /* No significance to these numbers, just enough to mix it up */
    statbase = g_get_real_time();
    stats->rd_req = statbase / 10;
    stats->rd_bytes = statbase / 20;
    stats->wr_req = statbase / 30;
    stats->wr_bytes = statbase / 40;
    stats->errs = statbase / (1000LL * 1000LL * 2);

    ret = 0;
 error:
    virDomainObjEndAPI(&privdom);
    return ret;
}


static int
sfvmDomainInterfaceAddressFromNet(sfvmDriver *driver,
                                  const virDomainNetDef *net,
                                  size_t addr_offset,
                                  virDomainInterfacePtr iface)
{
    virSocketAddr addr;
    virNetworkObj *net_obj = NULL;
    virNetworkDef *net_def = NULL;
    int ret = -1;

    if (!(net_obj = sfvmNetworkObjFindByName(driver, net->data.network.name)))
        return -1;

    net_def = virNetworkObjGetDef(net_obj);

    iface->addrs[0].prefix = virSocketAddrGetIPPrefix(&net_def->ips->address,
                                                      &net_def->ips->netmask,
                                                      net_def->ips->prefix);

    if (net_def->ips->nranges > 0)
        addr = net_def->ips->ranges[0].addr.start;
    else
        addr = net_def->ips->address;

    if (net_def->ips->family && STREQ(net_def->ips->family, "ipv6")) {
        iface->addrs[0].type = VIR_IP_ADDR_TYPE_IPV6;
        addr.data.inet6.sin6_addr.s6_addr[15] += addr_offset;
    } else {
        iface->addrs[0].type = VIR_IP_ADDR_TYPE_IPV4;
        addr.data.inet4.sin_addr.s_addr = \
            htonl(ntohl(addr.data.inet4.sin_addr.s_addr) + addr_offset);
    }

    if (!(iface->addrs[0].addr = virSocketAddrFormat(&addr)))
        goto cleanup;

    ret = 0;
 cleanup:
    virNetworkObjEndAPI(&net_obj);
    return ret;
}

static int
sfvmDomainGetSecurityLabel(virDomainPtr dom,
                           virSecurityLabelPtr seclabel)
{
    virDomainObj *vm;
    int ret = -1;

    memset(seclabel, 0, sizeof(*seclabel));

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjIsActive(vm)) {
        if (virStrcpyStatic(seclabel->label, "libvirt-sfvm") < 0) {
            virReportError(VIR_ERR_INTERNAL_ERROR,
                           _("security label exceeds maximum: %zu"),
                           sizeof(seclabel->label) - 1);
            goto cleanup;
        }

        seclabel->enforcing = 1;
    }

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmNodeGetSecurityModel(virConnectPtr conn,
                         virSecurityModelPtr secmodel)
{
    sfvmDriver *driver = conn->privateData;

    memset(secmodel, 0, sizeof(*secmodel));

    if (driver->caps->host.nsecModels == 0 ||
        driver->caps->host.secModels[0].model == NULL)
        return 0;

    if (virStrcpy(secmodel->model, driver->caps->host.secModels[0].model,
                  VIR_SECURITY_MODEL_BUFLEN) < 0) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("security model string exceeds max %d bytes"),
                       VIR_SECURITY_MODEL_BUFLEN - 1);
        return -1;
    }

    if (virStrcpy(secmodel->doi, driver->caps->host.secModels[0].doi,
                  VIR_SECURITY_DOI_BUFLEN) < 0) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("security DOI string exceeds max %d bytes"),
                       VIR_SECURITY_DOI_BUFLEN - 1);
        return -1;
    }

    return 0;
}

static int
sfvmDomainInterfaceAddresses(virDomainPtr dom,
                             virDomainInterfacePtr **ifaces,
                             unsigned int source,
                             unsigned int flags)
{
    size_t i;
    size_t ifaces_count = 0;
    int ret = -1;
    char macaddr[VIR_MAC_STRING_BUFLEN];
    virDomainObj *vm = NULL;
    virDomainInterfacePtr iface = NULL;
    virDomainInterfacePtr *ifaces_ret = NULL;

    virCheckFlags(0, -1);

    if (source >= VIR_DOMAIN_INTERFACE_ADDRESSES_SRC_LAST) {
        virReportError(VIR_ERR_ARGUMENT_UNSUPPORTED,
                       _("Unknown IP address data source %d"),
                       source);
        return -1;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    ifaces_ret = g_new0(virDomainInterfacePtr, vm->def->nnets);

    for (i = 0; i < vm->def->nnets; i++) {
        const virDomainNetDef *net = vm->def->nets[i];

        iface = g_new0(virDomainInterface, 1);

        iface->name = g_strdup(net->ifname);

        virMacAddrFormat(&net->mac, macaddr);
        iface->hwaddr = g_strdup(macaddr);

        iface->addrs = g_new0(virDomainIPAddress, 1);
        iface->naddrs = 1;

        if (net->type == VIR_DOMAIN_NET_TYPE_NETWORK) {
            /* try using different addresses per different inf and domain */
            const size_t addr_offset = 20 * (vm->def->id - 1) + i + 1;

            if (sfvmDomainInterfaceAddressFromNet(dom->conn->privateData,
                                                  net, addr_offset, iface) < 0)
                goto cleanup;
        } else {
            iface->addrs[0].type = VIR_IP_ADDR_TYPE_IPV4;
            iface->addrs[0].prefix = 24;
            iface->addrs[0].addr = g_strdup_printf("192.168.0.%zu", 1 + i);

        }

        VIR_APPEND_ELEMENT_INPLACE(ifaces_ret, ifaces_count, iface);
    }

    *ifaces = g_steal_pointer(&ifaces_ret);
    ret = ifaces_count;

 cleanup:
    virDomainObjEndAPI(&vm);

    if (ifaces_ret) {
        for (i = 0; i < ifaces_count; i++)
            virDomainInterfaceFree(ifaces_ret[i]);
    }
    virDomainInterfaceFree(iface);

    VIR_FREE(ifaces_ret);
    return ret;
}

static int
sfvmDomainInterfaceStats(virDomainPtr domain,
                         const char *device,
                         virDomainInterfaceStatsPtr stats)
{
    virDomainObj *privdom;
    unsigned long long statbase;
    virDomainNetDef *net = NULL;
    int ret = -1;


    if (!(privdom = sfvmDomObjFromDomain(domain)))
        return -1;

    if (virDomainObjCheckActive(privdom) < 0)
        goto error;

    if (!(net = virDomainNetFind(privdom->def, device)))
        goto error;

    /* No significance to these numbers, just enough to mix it up */
    statbase = g_get_real_time();
    stats->rx_bytes = statbase / 10;
    stats->rx_packets = statbase / 100;
    stats->rx_errs = statbase / (1000LL * 1000LL * 1);
    stats->rx_drop = statbase / (1000LL * 1000LL * 2);
    stats->tx_bytes = statbase / 20;
    stats->tx_packets = statbase / 110;
    stats->tx_errs = statbase / (1000LL * 1000LL * 3);
    stats->tx_drop = statbase / (1000LL * 1000LL * 4);

    ret = 0;
 error:
    virDomainObjEndAPI(&privdom);
    return ret;
}


static virNetworkObj *
sfvmNetworkObjFindByUUID(sfvmDriver *privconn,
                         const unsigned char *uuid)
{
    virNetworkObj *obj;
    char uuidstr[VIR_UUID_STRING_BUFLEN];

    if (!(obj = virNetworkObjFindByUUID(privconn->networks, uuid))) {
        virUUIDFormat(uuid, uuidstr);
        virReportError(VIR_ERR_NO_NETWORK,
                       _("no network with matching uuid '%s'"),
                       uuidstr);
    }

    return obj;
}


static virNetworkPtr
sfvmNetworkLookupByUUID(virConnectPtr conn,
                        const unsigned char *uuid)
{
    sfvmDriver *privconn = conn->privateData;
    virNetworkObj *obj;
    virNetworkDef *def;
    virNetworkPtr net = NULL;

    if (!(obj = sfvmNetworkObjFindByUUID(privconn, uuid)))
        goto cleanup;
    def = virNetworkObjGetDef(obj);

    net = virGetNetwork(conn, def->name, def->uuid);

 cleanup:
    virNetworkObjEndAPI(&obj);
    return net;
}


static virNetworkObj *
sfvmNetworkObjFindByName(sfvmDriver *privconn,
                         const char *name)
{
    virNetworkObj *obj;

    if (!(obj = virNetworkObjFindByName(privconn->networks, name)))
        virReportError(VIR_ERR_NO_NETWORK,
                       _("no network with matching name '%s'"),
                       name);

    return obj;
}


static virNetworkPtr
sfvmNetworkLookupByName(virConnectPtr conn,
                        const char *name)
{
    sfvmDriver *privconn = conn->privateData;
    virNetworkObj *obj;
    virNetworkDef *def;
    virNetworkPtr net = NULL;

    if (!(obj = sfvmNetworkObjFindByName(privconn, name)))
        goto cleanup;
    def = virNetworkObjGetDef(obj);

    net = virGetNetwork(conn, def->name, def->uuid);

 cleanup:
    virNetworkObjEndAPI(&obj);
    return net;
}


static int
sfvmConnectNumOfNetworks(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    return virNetworkObjListNumOfNetworks(privconn->networks, true, NULL,
                                          conn);
}


static int
sfvmConnectListNetworks(virConnectPtr conn,
                        char **const names,
                        int maxnames)
{
    sfvmDriver *privconn = conn->privateData;
    return virNetworkObjListGetNames(privconn->networks, true, names,
                                     maxnames, NULL, conn);
}


static int
sfvmConnectNumOfDefinedNetworks(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    return virNetworkObjListNumOfNetworks(privconn->networks, false, NULL,
                                          conn);
}


static int
sfvmConnectListDefinedNetworks(virConnectPtr conn,
                               char **const names,
                               int maxnames)
{
    sfvmDriver *privconn = conn->privateData;
    return virNetworkObjListGetNames(privconn->networks, false, names,
                                     maxnames, NULL, conn);
}


static int
sfvmConnectListAllNetworks(virConnectPtr conn,
                           virNetworkPtr **nets,
                           unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;

    virCheckFlags(VIR_CONNECT_LIST_NETWORKS_FILTERS_ALL, -1);

    return virNetworkObjListExport(conn, privconn->networks, nets, NULL, flags);
}


static int
sfvmNetworkIsActive(virNetworkPtr net)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    int ret = -1;

    if (!(obj = sfvmNetworkObjFindByUUID(privconn, net->uuid)))
        goto cleanup;

    ret = virNetworkObjIsActive(obj);

 cleanup:
    virNetworkObjEndAPI(&obj);
    return ret;
}


static int
sfvmNetworkIsPersistent(virNetworkPtr net)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    int ret = -1;

    if (!(obj = sfvmNetworkObjFindByUUID(privconn, net->uuid)))
        goto cleanup;

    ret = virNetworkObjIsPersistent(obj);

 cleanup:
    virNetworkObjEndAPI(&obj);
    return ret;
}


static virNetworkPtr
sfvmNetworkCreateXMLFlags(virConnectPtr conn, const char *xml,
                          unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    g_autoptr(virNetworkDef) newDef = NULL;
    virNetworkObj *obj = NULL;
    virNetworkDef *def;
    virNetworkPtr net = NULL;
    virObjectEvent *event = NULL;

    virCheckFlags(VIR_NETWORK_CREATE_VALIDATE, NULL);

    if (!(newDef = virNetworkDefParse(xml, NULL, NULL,
                                      !!(flags & VIR_NETWORK_CREATE_VALIDATE))))
        goto cleanup;

    if (!(obj = virNetworkObjAssignDef(privconn->networks, newDef,
                                       VIR_NETWORK_OBJ_LIST_ADD_LIVE |
                                       VIR_NETWORK_OBJ_LIST_ADD_CHECK_LIVE)))
        goto cleanup;
    newDef = NULL;
    def = virNetworkObjGetDef(obj);
    virNetworkObjSetActive(obj, true);

    event = virNetworkEventLifecycleNew(def->name, def->uuid,
                                        VIR_NETWORK_EVENT_STARTED,
                                        0);

    net = virGetNetwork(conn, def->name, def->uuid);

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virNetworkObjEndAPI(&obj);
    return net;
}


static virNetworkPtr
sfvmNetworkCreateXML(virConnectPtr conn, const char *xml)
{
    return sfvmNetworkCreateXMLFlags(conn, xml, 0);
}


static virNetworkPtr
sfvmNetworkDefineXMLFlags(virConnectPtr conn,
                          const char *xml,
                          unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    g_autoptr(virNetworkDef) newDef = NULL;
    virNetworkObj *obj = NULL;
    virNetworkDef *def;
    virNetworkPtr net = NULL;
    virObjectEvent *event = NULL;

    virCheckFlags(VIR_NETWORK_DEFINE_VALIDATE, NULL);

    if (!(newDef = virNetworkDefParse(xml, NULL, NULL,
                                      !!(flags & VIR_NETWORK_DEFINE_VALIDATE))))
        goto cleanup;

    if (!(obj = virNetworkObjAssignDef(privconn->networks, newDef, 0)))
        goto cleanup;
    newDef = NULL;
    def = virNetworkObjGetDef(obj);

    event = virNetworkEventLifecycleNew(def->name, def->uuid,
                                        VIR_NETWORK_EVENT_DEFINED,
                                        0);

    net = virGetNetwork(conn, def->name, def->uuid);

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virNetworkObjEndAPI(&obj);
    return net;
}


static virNetworkPtr
sfvmNetworkDefineXML(virConnectPtr conn,
                     const char *xml)
{
    return sfvmNetworkDefineXMLFlags(conn, xml, 0);
}


static int
sfvmNetworkUndefine(virNetworkPtr net)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    int ret = -1;
    virObjectEvent *event = NULL;

    if (!(obj = sfvmNetworkObjFindByName(privconn, net->name)))
        goto cleanup;

    if (virNetworkObjIsActive(obj)) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       _("Network '%s' is still running"), net->name);
        goto cleanup;
    }

    event = virNetworkEventLifecycleNew(net->name, net->uuid,
                                        VIR_NETWORK_EVENT_UNDEFINED,
                                        0);

    virNetworkObjRemoveInactive(privconn->networks, obj);
    ret = 0;

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virNetworkObjEndAPI(&obj);
    return ret;
}


static int
sfvmNetworkUpdate(virNetworkPtr net,
                  unsigned int command,
                  unsigned int section,
                  int parentIndex,
                  const char *xml,
                  unsigned int flags)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj = NULL;
    int isActive, ret = -1;

    virCheckFlags(VIR_NETWORK_UPDATE_AFFECT_LIVE |
                  VIR_NETWORK_UPDATE_AFFECT_CONFIG,
                  -1);

    if (!(obj = sfvmNetworkObjFindByUUID(privconn, net->uuid)))
        goto cleanup;

    /* VIR_NETWORK_UPDATE_AFFECT_CURRENT means "change LIVE if network
     * is active, else change CONFIG
    */
    isActive = virNetworkObjIsActive(obj);
    if ((flags & (VIR_NETWORK_UPDATE_AFFECT_LIVE
                   | VIR_NETWORK_UPDATE_AFFECT_CONFIG)) ==
        VIR_NETWORK_UPDATE_AFFECT_CURRENT) {
        if (isActive)
            flags |= VIR_NETWORK_UPDATE_AFFECT_LIVE;
        else
            flags |= VIR_NETWORK_UPDATE_AFFECT_CONFIG;
    }

    /* update the network config in memory/on disk */
    if (virNetworkObjUpdate(obj, command, section,
                            parentIndex, xml, NULL, flags) < 0)
       goto cleanup;

    ret = 0;
 cleanup:
    virNetworkObjEndAPI(&obj);
    return ret;
}


static int
sfvmNetworkCreate(virNetworkPtr net)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    virNetworkDef *def;
    int ret = -1;
    virObjectEvent *event = NULL;

    if (!(obj = sfvmNetworkObjFindByName(privconn, net->name)))
        goto cleanup;
    def = virNetworkObjGetDef(obj);

    if (virNetworkObjIsActive(obj)) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       _("Network '%s' is already running"), net->name);
        goto cleanup;
    }

    virNetworkObjSetActive(obj, true);
    event = virNetworkEventLifecycleNew(def->name, def->uuid,
                                        VIR_NETWORK_EVENT_STARTED,
                                        0);
    ret = 0;

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virNetworkObjEndAPI(&obj);
    return ret;
}


static int
sfvmNetworkDestroy(virNetworkPtr net)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    virNetworkDef *def;
    int ret = -1;
    virObjectEvent *event = NULL;

    if (!(obj = sfvmNetworkObjFindByName(privconn, net->name)))
        goto cleanup;
    def = virNetworkObjGetDef(obj);

    virNetworkObjSetActive(obj, false);
    event = virNetworkEventLifecycleNew(def->name, def->uuid,
                                        VIR_NETWORK_EVENT_STOPPED,
                                        0);
    if (!virNetworkObjIsPersistent(obj))
        virNetworkObjRemoveInactive(privconn->networks, obj);

    ret = 0;

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virNetworkObjEndAPI(&obj);
    return ret;
}


static char *
sfvmNetworkGetXMLDesc(virNetworkPtr net,
                      unsigned int flags)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    char *ret = NULL;

    virCheckFlags(0, NULL);

    if (!(obj = sfvmNetworkObjFindByName(privconn, net->name)))
        goto cleanup;

    ret = virNetworkDefFormat(virNetworkObjGetDef(obj), NULL, flags);

 cleanup:
    virNetworkObjEndAPI(&obj);
    return ret;
}


static char *
sfvmNetworkGetBridgeName(virNetworkPtr net)
{
    sfvmDriver *privconn = net->conn->privateData;
    char *bridge = NULL;
    virNetworkObj *obj;
    virNetworkDef *def;

    if (!(obj = sfvmNetworkObjFindByName(privconn, net->name)))
        goto cleanup;
    def = virNetworkObjGetDef(obj);

    if (!(def->bridge)) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("network '%s' does not have a bridge name."),
                       def->name);
        goto cleanup;
    }

    bridge = g_strdup(def->bridge);

 cleanup:
    virNetworkObjEndAPI(&obj);
    return bridge;
}


static int
sfvmNetworkGetAutostart(virNetworkPtr net,
                        int *autostart)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    int ret = -1;

    if (!(obj = sfvmNetworkObjFindByName(privconn, net->name)))
        goto cleanup;

    *autostart = virNetworkObjIsAutostart(obj) ? 1 : 0;
    ret = 0;

 cleanup:
    virNetworkObjEndAPI(&obj);
    return ret;
}


static int
sfvmNetworkSetAutostart(virNetworkPtr net,
                        int autostart)
{
    sfvmDriver *privconn = net->conn->privateData;
    virNetworkObj *obj;
    bool new_autostart = (autostart != 0);
    int ret = -1;

    if (!(obj = sfvmNetworkObjFindByName(privconn, net->name)))
        goto cleanup;

    virNetworkObjSetAutostart(obj, new_autostart);

    ret = 0;

 cleanup:
    virNetworkObjEndAPI(&obj);
    return ret;
}


/*
 * Physical host interface routines
 */


static virInterfaceObj *
sfvmInterfaceObjFindByName(sfvmDriver *privconn,
                           const char *name)
{
    virInterfaceObj *obj;

    virObjectLock(privconn);
    obj = virInterfaceObjListFindByName(privconn->ifaces, name);
    virObjectUnlock(privconn);

    if (!obj)
        virReportError(VIR_ERR_NO_INTERFACE,
                       _("no interface with matching name '%s'"),
                       name);

    return obj;
}


static int
sfvmConnectNumOfInterfaces(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    int ninterfaces;

    virObjectLock(privconn);
    ninterfaces = virInterfaceObjListNumOfInterfaces(privconn->ifaces, true);
    virObjectUnlock(privconn);
    return ninterfaces;
}


static int
sfvmConnectListInterfaces(virConnectPtr conn,
                          char **const names,
                          int maxnames)
{
    sfvmDriver *privconn = conn->privateData;
    int nnames;

    virObjectLock(privconn);
    nnames = virInterfaceObjListGetNames(privconn->ifaces, true,
                                         names, maxnames);
    virObjectUnlock(privconn);

    return nnames;
}


static int
sfvmConnectNumOfDefinedInterfaces(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    int ninterfaces;

    virObjectLock(privconn);
    ninterfaces = virInterfaceObjListNumOfInterfaces(privconn->ifaces, false);
    virObjectUnlock(privconn);
    return ninterfaces;
}


static int
sfvmConnectListDefinedInterfaces(virConnectPtr conn,
                                 char **const names,
                                 int maxnames)
{
    sfvmDriver *privconn = conn->privateData;
    int nnames;

    virObjectLock(privconn);
    nnames = virInterfaceObjListGetNames(privconn->ifaces, false,
                                         names, maxnames);
    virObjectUnlock(privconn);

    return nnames;
}


static int
sfvmConnectListAllInterfaces(virConnectPtr conn,
                             virInterfacePtr **ifaces,
                             unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;

    virCheckFlags(VIR_CONNECT_LIST_INTERFACES_FILTERS_ACTIVE, -1);

    return virInterfaceObjListExport(conn, privconn->ifaces, ifaces,
                                     NULL, flags);
}


static virInterfacePtr
sfvmInterfaceLookupByName(virConnectPtr conn,
                          const char *name)
{
    sfvmDriver *privconn = conn->privateData;
    virInterfaceObj *obj;
    virInterfaceDef *def;
    virInterfacePtr ret = NULL;

    if (!(obj = sfvmInterfaceObjFindByName(privconn, name)))
        return NULL;
    def = virInterfaceObjGetDef(obj);

    ret = virGetInterface(conn, def->name, def->mac);

    virInterfaceObjEndAPI(&obj);
    return ret;
}


static virInterfacePtr
sfvmInterfaceLookupByMACString(virConnectPtr conn,
                               const char *mac)
{
    sfvmDriver *privconn = conn->privateData;
    int ifacect;
    char *ifacenames[] = { NULL, NULL };
    virInterfacePtr ret = NULL;

    virObjectLock(privconn);
    ifacect = virInterfaceObjListFindByMACString(privconn->ifaces, mac,
                                                 ifacenames, 2);
    virObjectUnlock(privconn);

    if (ifacect == 0) {
        virReportError(VIR_ERR_NO_INTERFACE,
                       _("no interface with matching mac '%s'"), mac);
        goto cleanup;
    }

    if (ifacect > 1) {
        virReportError(VIR_ERR_MULTIPLE_INTERFACES, NULL);
        goto cleanup;
    }

    ret = virGetInterface(conn, ifacenames[0], mac);

 cleanup:
    VIR_FREE(ifacenames[0]);
    VIR_FREE(ifacenames[1]);
    return ret;
}


static int
sfvmInterfaceIsActive(virInterfacePtr iface)
{
    sfvmDriver *privconn = iface->conn->privateData;
    virInterfaceObj *obj;
    int ret = -1;

    if (!(obj = sfvmInterfaceObjFindByName(privconn, iface->name)))
        return -1;

    ret = virInterfaceObjIsActive(obj);

    virInterfaceObjEndAPI(&obj);
    return ret;
}


static int
sfvmInterfaceChangeBegin(virConnectPtr conn,
                         unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    int ret = -1;

    virCheckFlags(0, -1);

    virObjectLock(privconn);
    if (privconn->transaction_running) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("there is another transaction running."));
        goto cleanup;
    }

    privconn->transaction_running = true;

    if (!(privconn->backupIfaces = virInterfaceObjListClone(privconn->ifaces)))
        goto cleanup;

    ret = 0;
 cleanup:
    virObjectUnlock(privconn);
    return ret;
}


static int
sfvmInterfaceChangeCommit(virConnectPtr conn,
                          unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    int ret = -1;

    virCheckFlags(0, -1);

    virObjectLock(privconn);

    if (!privconn->transaction_running) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("no transaction running, "
                         "nothing to be committed."));
        goto cleanup;
    }

    virObjectUnref(privconn->backupIfaces);
    privconn->transaction_running = false;

    ret = 0;

 cleanup:
    virObjectUnlock(privconn);

    return ret;
}


static int
sfvmInterfaceChangeRollback(virConnectPtr conn,
                            unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    int ret = -1;

    virCheckFlags(0, -1);

    virObjectLock(privconn);

    if (!privconn->transaction_running) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("no transaction running, "
                         "nothing to rollback."));
        goto cleanup;
    }

    virObjectUnref(privconn->ifaces);
    privconn->ifaces = g_steal_pointer(&privconn->backupIfaces);

    privconn->transaction_running = false;

    ret = 0;

 cleanup:
    virObjectUnlock(privconn);
    return ret;
}


static char *
sfvmInterfaceGetXMLDesc(virInterfacePtr iface,
                        unsigned int flags)
{
    sfvmDriver *privconn = iface->conn->privateData;
    virInterfaceObj *obj;
    virInterfaceDef *def;
    char *ret = NULL;

    virCheckFlags(0, NULL);

    if (!(obj = sfvmInterfaceObjFindByName(privconn, iface->name)))
        return NULL;
    def = virInterfaceObjGetDef(obj);

    ret = virInterfaceDefFormat(def);

    virInterfaceObjEndAPI(&obj);
    return ret;
}


static virInterfacePtr
sfvmInterfaceDefineXML(virConnectPtr conn,
                       const char *xmlStr,
                       unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    g_autoptr(virInterfaceDef) def = NULL;
    virInterfaceObj *obj = NULL;
    virInterfaceDef *objdef;
    virInterfacePtr ret = NULL;

    virCheckFlags(VIR_INTERFACE_DEFINE_VALIDATE, NULL);

    virObjectLock(privconn);
    if ((def = virInterfaceDefParseString(xmlStr, flags)) == NULL)
        goto cleanup;

    if ((obj = virInterfaceObjListAssignDef(privconn->ifaces, &def)) == NULL)
        goto cleanup;
    objdef = virInterfaceObjGetDef(obj);

    ret = virGetInterface(conn, objdef->name, objdef->mac);

 cleanup:
    virInterfaceObjEndAPI(&obj);
    virObjectUnlock(privconn);
    return ret;
}


static int
sfvmInterfaceUndefine(virInterfacePtr iface)
{
    sfvmDriver *privconn = iface->conn->privateData;
    virInterfaceObj *obj;

    if (!(obj = sfvmInterfaceObjFindByName(privconn, iface->name)))
        return -1;

    virInterfaceObjListRemove(privconn->ifaces, obj);
    virObjectUnref(obj);

    return 0;
}


static int
sfvmInterfaceCreate(virInterfacePtr iface,
                    unsigned int flags)
{
    sfvmDriver *privconn = iface->conn->privateData;
    virInterfaceObj *obj;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(obj = sfvmInterfaceObjFindByName(privconn, iface->name)))
        return -1;

    if (virInterfaceObjIsActive(obj)) {
        virReportError(VIR_ERR_OPERATION_INVALID, NULL);
        goto cleanup;
    }

    virInterfaceObjSetActive(obj, true);
    ret = 0;

 cleanup:
    virInterfaceObjEndAPI(&obj);
    return ret;
}


static int
sfvmInterfaceDestroy(virInterfacePtr iface,
                     unsigned int flags)
{
    sfvmDriver *privconn = iface->conn->privateData;
    virInterfaceObj *obj;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(obj = sfvmInterfaceObjFindByName(privconn, iface->name)))
        return -1;

    if (!virInterfaceObjIsActive(obj)) {
        virReportError(VIR_ERR_OPERATION_INVALID, NULL);
        goto cleanup;
    }

    virInterfaceObjSetActive(obj, false);
    ret = 0;

 cleanup:
    virInterfaceObjEndAPI(&obj);
    return ret;
}



/*
 * Storage Driver routines
 */

static int
sfvmStoragePoolObjSetDefaults(virStoragePoolObj *obj)
{
    char *configFile;
    virStoragePoolDef *def = virStoragePoolObjGetDef(obj);

    def->capacity = defaultPoolCap;
    def->allocation = defaultPoolAlloc;
    def->available = defaultPoolCap - defaultPoolAlloc;

    configFile = g_strdup("");

    virStoragePoolObjSetConfigFile(obj, configFile);
    return 0;
}


static virStoragePoolObj *
sfvmStoragePoolObjFindByName(sfvmDriver *privconn,
                             const char *name)
{
    virStoragePoolObj *obj;

    virObjectLock(privconn);
    obj = virStoragePoolObjFindByName(privconn->pools, name);
    virObjectUnlock(privconn);

    if (!obj)
        virReportError(VIR_ERR_NO_STORAGE_POOL,
                       _("no storage pool with matching name '%s'"),
                       name);

    return obj;
}


static virStoragePoolObj *
sfvmStoragePoolObjFindActiveByName(sfvmDriver *privconn,
                                   const char *name)
{
    virStoragePoolObj *obj;

    if (!(obj = sfvmStoragePoolObjFindByName(privconn, name)))
        return NULL;

    if (!virStoragePoolObjIsActive(obj)) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       _("storage pool '%s' is not active"), name);
        virStoragePoolObjEndAPI(&obj);
        return NULL;
    }

    return obj;
}


static virStoragePoolObj *
sfvmStoragePoolObjFindInactiveByName(sfvmDriver *privconn,
                                     const char *name)
{
    virStoragePoolObj *obj;

    if (!(obj = sfvmStoragePoolObjFindByName(privconn, name)))
        return NULL;

    if (virStoragePoolObjIsActive(obj)) {
        virReportError(VIR_ERR_OPERATION_INVALID,
                       _("storage pool '%s' is active"), name);
        virStoragePoolObjEndAPI(&obj);
        return NULL;
    }

    return obj;
}


static virStoragePoolObj *
sfvmStoragePoolObjFindByUUID(sfvmDriver *privconn,
                             const unsigned char *uuid)
{
    virStoragePoolObj *obj;
    char uuidstr[VIR_UUID_STRING_BUFLEN];

    virObjectLock(privconn);
    obj = virStoragePoolObjFindByUUID(privconn->pools, uuid);
    virObjectUnlock(privconn);

    if (!obj) {
        virUUIDFormat(uuid, uuidstr);
        virReportError(VIR_ERR_NO_STORAGE_POOL,
                       _("no storage pool with matching uuid '%s'"),
                       uuidstr);
    }

    return obj;
}


static virStoragePoolPtr
sfvmStoragePoolLookupByUUID(virConnectPtr conn,
                            const unsigned char *uuid)
{
    sfvmDriver *privconn = conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    virStoragePoolPtr pool = NULL;

    if (!(obj = sfvmStoragePoolObjFindByUUID(privconn, uuid)))
        return NULL;
    def = virStoragePoolObjGetDef(obj);

    pool = virGetStoragePool(conn, def->name, def->uuid, NULL, NULL);

    virStoragePoolObjEndAPI(&obj);
    return pool;
}


static virStoragePoolPtr
sfvmStoragePoolLookupByName(virConnectPtr conn,
                            const char *name)
{
    sfvmDriver *privconn = conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    virStoragePoolPtr pool = NULL;

    if (!(obj = sfvmStoragePoolObjFindByName(privconn, name)))
        return NULL;
    def = virStoragePoolObjGetDef(obj);

    pool = virGetStoragePool(conn, def->name, def->uuid, NULL, NULL);

    virStoragePoolObjEndAPI(&obj);
    return pool;
}


static virStoragePoolPtr
sfvmStoragePoolLookupByVolume(virStorageVolPtr vol)
{
    return sfvmStoragePoolLookupByName(vol->conn, vol->pool);
}


static int
sfvmConnectNumOfStoragePools(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    int numActive = 0;

    virObjectLock(privconn);
    numActive = virStoragePoolObjNumOfStoragePools(privconn->pools, conn,
                                                   true, NULL);
    virObjectUnlock(privconn);

    return numActive;
}


static int
sfvmConnectListStoragePools(virConnectPtr conn,
                            char **const names,
                            int maxnames)
{
    sfvmDriver *privconn = conn->privateData;
    int n = 0;

    virObjectLock(privconn);
    n = virStoragePoolObjGetNames(privconn->pools, conn, true, NULL,
                                  names, maxnames);
    virObjectUnlock(privconn);

    return n;
}


static int
sfvmConnectNumOfDefinedStoragePools(virConnectPtr conn)
{
    sfvmDriver *privconn = conn->privateData;
    int numInactive = 0;

    virObjectLock(privconn);
    numInactive = virStoragePoolObjNumOfStoragePools(privconn->pools, conn,
                                                     false, NULL);
    virObjectUnlock(privconn);

    return numInactive;
}


static int
sfvmConnectListDefinedStoragePools(virConnectPtr conn,
                                   char **const names,
                                   int maxnames)
{
    sfvmDriver *privconn = conn->privateData;
    int n = 0;

    virObjectLock(privconn);
    n = virStoragePoolObjGetNames(privconn->pools, conn, false, NULL,
                                  names, maxnames);
    virObjectUnlock(privconn);

    return n;
}


static int
sfvmConnectListAllStoragePools(virConnectPtr conn,
                               virStoragePoolPtr **pools,
                               unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    int ret = -1;

    virCheckFlags(VIR_CONNECT_LIST_STORAGE_POOLS_FILTERS_ALL, -1);

    virObjectLock(privconn);
    ret = virStoragePoolObjListExport(conn, privconn->pools, pools,
                                      NULL, flags);
    virObjectUnlock(privconn);

    return ret;
}


static int
sfvmStoragePoolIsActive(virStoragePoolPtr pool)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    int ret = -1;

    if (!(obj = sfvmStoragePoolObjFindByUUID(privconn, pool->uuid)))
        goto cleanup;

    ret = virStoragePoolObjIsActive(obj);

 cleanup:
    if (obj)
        virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStoragePoolIsPersistent(virStoragePoolPtr pool)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    int ret = -1;

    if (!(obj = sfvmStoragePoolObjFindByUUID(privconn, pool->uuid)))
        return -1;

    ret = virStoragePoolObjGetConfigFile(obj) ? 1 : 0;

    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStoragePoolCreate(virStoragePoolPtr pool,
                      unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virObjectEvent *event = NULL;

    virCheckFlags(0, -1);

    if (!(obj = sfvmStoragePoolObjFindInactiveByName(privconn, pool->name)))
        return -1;

    virStoragePoolObjSetActive(obj, true);

    event = virStoragePoolEventLifecycleNew(pool->name, pool->uuid,
                                            VIR_STORAGE_POOL_EVENT_STARTED,
                                            0);

    virObjectEventStateQueue(privconn->eventState, event);
    virStoragePoolObjEndAPI(&obj);
    return 0;
}


static char *
sfvmConnectFindStoragePoolSources(virConnectPtr conn G_GNUC_UNUSED,
                                  const char *type,
                                  const char *srcSpec,
                                  unsigned int flags)
{
    int pool_type;
    char *ret = NULL;
    g_autoptr(virStoragePoolSource) source = NULL;

    virCheckFlags(0, NULL);

    pool_type = virStoragePoolTypeFromString(type);
    if (!pool_type) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("unknown storage pool type %s"), type);
        return NULL;
    }

    if (srcSpec) {
        source = virStoragePoolDefParseSourceString(srcSpec, pool_type);
        if (!source)
            return NULL;
    }

    switch (pool_type) {

    case VIR_STORAGE_POOL_LOGICAL:
        ret = g_strdup(defaultPoolSourcesLogicalXML);
        return ret;

    case VIR_STORAGE_POOL_NETFS:
        if (!source || !source->hosts[0].name) {
            virReportError(VIR_ERR_INVALID_ARG,
                           "%s", _("hostname must be specified for netfs sources"));
            return NULL;
        }

        ret = g_strdup_printf(defaultPoolSourcesNetFSXML, source->hosts[0].name);
        return ret;

    default:
        virReportError(VIR_ERR_NO_SUPPORT,
                       _("pool type '%s' does not support source discovery"), type);
    }

    return NULL;
}


static virNodeDeviceObj *
sfvmNodeDeviceMockCreateVport(sfvmDriver *driver,
                              const char *wwnn,
                              const char *wwpn);
static int
sfvmCreateVport(sfvmDriver *driver,
                const char *wwnn,
                const char *wwpn)
{
    virNodeDeviceObj *obj = NULL;
    /* The storage_backend_scsi createVport() will use the input adapter
     * fields parent name, parent_wwnn/parent_wwpn, or parent_fabric_wwn
     * in order to determine whether the provided parent can be used to
     * create a vHBA or will find "an available vport capable" to create
     * a vHBA. In order to do this, it uses the virVHBA* API's which traverse
     * the sysfs looking at various fields (rather than going via nodedev).
     *
     * Since the sfvm environ doesn't have the sysfs for the storage pool
     * sfvm, at least for now use the node device sfvm infrastructure to
     * create the vHBA. In the long run the result is the same. */
    if (!(obj = sfvmNodeDeviceMockCreateVport(driver, wwnn, wwpn)))
        return -1;
    virNodeDeviceObjEndAPI(&obj);

    return 0;
}


static virStoragePoolPtr
sfvmStoragePoolCreateXML(virConnectPtr conn,
                         const char *xml,
                         unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    virStoragePoolObj *obj = NULL;
    virStoragePoolDef *def;
    virStoragePoolPtr pool = NULL;
    virObjectEvent *event = NULL;
    g_autoptr(virStoragePoolDef) newDef = NULL;

    virCheckFlags(0, NULL);

    virObjectLock(privconn);
    if (!(newDef = virStoragePoolDefParse(xml, NULL, 0)))
        goto cleanup;

    if (!(obj = virStoragePoolObjListAdd(privconn->pools, &newDef,
                                         VIR_STORAGE_POOL_OBJ_LIST_ADD_CHECK_LIVE)))
        goto cleanup;
    def = virStoragePoolObjGetDef(obj);

    if (def->source.adapter.type == VIR_STORAGE_ADAPTER_TYPE_FC_HOST) {
        /* In the real code, we'd call virVHBAManageVport followed by
         * find_new_device, but we cannot do that here since we're not
         * mocking udev. The mock routine will copy an existing vHBA and
         * rename a few fields to mock that. */
        if (sfvmCreateVport(privconn,
                            def->source.adapter.data.fchost.wwnn,
                            def->source.adapter.data.fchost.wwpn) < 0) {
            virStoragePoolObjRemove(privconn->pools, obj);
            goto cleanup;
        }
    }

    if (sfvmStoragePoolObjSetDefaults(obj) == -1) {
        virStoragePoolObjRemove(privconn->pools, obj);
        goto cleanup;
    }

    /* *SetDefaults fills this in for the persistent pools, but this
     * would be a transient pool so remove it; otherwise, the Destroy
     * code will not Remove the pool */
    virStoragePoolObjSetConfigFile(obj, NULL);

    virStoragePoolObjSetActive(obj, true);

    event = virStoragePoolEventLifecycleNew(def->name, def->uuid,
                                            VIR_STORAGE_POOL_EVENT_STARTED,
                                            0);

    pool = virGetStoragePool(conn, def->name, def->uuid, NULL, NULL);

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virStoragePoolObjEndAPI(&obj);
    virObjectUnlock(privconn);
    return pool;
}


static virStoragePoolPtr
sfvmStoragePoolDefineXML(virConnectPtr conn,
                         const char *xml,
                         unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;
    virStoragePoolObj *obj = NULL;
    virStoragePoolDef *def;
    virStoragePoolPtr pool = NULL;
    virObjectEvent *event = NULL;
    g_autoptr(virStoragePoolDef) newDef = NULL;

    virCheckFlags(VIR_STORAGE_POOL_DEFINE_VALIDATE, NULL);

    virObjectLock(privconn);
    if (!(newDef = virStoragePoolDefParse(xml, NULL, flags)))
        goto cleanup;

    newDef->capacity = defaultPoolCap;
    newDef->allocation = defaultPoolAlloc;
    newDef->available = defaultPoolCap - defaultPoolAlloc;

    if (!(obj = virStoragePoolObjListAdd(privconn->pools, &newDef, 0)))
        goto cleanup;
    def = virStoragePoolObjGetDef(obj);

    event = virStoragePoolEventLifecycleNew(def->name, def->uuid,
                                            VIR_STORAGE_POOL_EVENT_DEFINED,
                                            0);

    if (sfvmStoragePoolObjSetDefaults(obj) == -1) {
        virStoragePoolObjRemove(privconn->pools, obj);
        goto cleanup;
    }

    pool = virGetStoragePool(conn, def->name, def->uuid, NULL, NULL);

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virStoragePoolObjEndAPI(&obj);
    virObjectUnlock(privconn);
    return pool;
}


static int
sfvmStoragePoolUndefine(virStoragePoolPtr pool)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virObjectEvent *event = NULL;

    if (!(obj = sfvmStoragePoolObjFindInactiveByName(privconn, pool->name)))
        return -1;

    event = virStoragePoolEventLifecycleNew(pool->name, pool->uuid,
                                            VIR_STORAGE_POOL_EVENT_UNDEFINED,
                                            0);

    virStoragePoolObjRemove(privconn->pools, obj);
    virStoragePoolObjEndAPI(&obj);

    virObjectEventStateQueue(privconn->eventState, event);
    return 0;
}


static int
sfvmStoragePoolBuild(virStoragePoolPtr pool,
                     unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virObjectEvent *event = NULL;

    virCheckFlags(0, -1);

    if (!(obj = sfvmStoragePoolObjFindInactiveByName(privconn, pool->name)))
        return -1;

    event = virStoragePoolEventLifecycleNew(pool->name, pool->uuid,
                                            VIR_STORAGE_POOL_EVENT_CREATED,
                                            0);

    virStoragePoolObjEndAPI(&obj);

    virObjectEventStateQueue(privconn->eventState, event);
    return 0;
}


static int
sfvmDestroyVport(sfvmDriver *privconn,
                 const char *wwnn G_GNUC_UNUSED,
                 const char *wwpn G_GNUC_UNUSED)
{
    virNodeDeviceObj *obj = NULL;
    virObjectEvent *event = NULL;

    /* NB: Cannot use virVHBAGetHostByWWN (yet) like the storage_backend_scsi
     * deleteVport() helper since that traverses the file system looking for
     * the wwnn/wwpn. So our choice short term is to cheat and use the name
     * (scsi_host12) we know was created.
     *
     * Reaching across the boundaries of space and time into the
     * Node Device in order to remove */
    if (!(obj = virNodeDeviceObjListFindByName(privconn->devs,
                                               "scsi_host12"))) {
        virReportError(VIR_ERR_NO_NODE_DEVICE, "%s",
                       _("no node device with matching name 'scsi_host12'"));
        return -1;
    }

    event = virNodeDeviceEventLifecycleNew("scsi_host12",
                                           VIR_NODE_DEVICE_EVENT_DELETED,
                                           0);

    virNodeDeviceObjListRemove(privconn->devs, obj);
    virNodeDeviceObjEndAPI(&obj);

    virObjectEventStateQueue(privconn->eventState, event);
    return 0;
}


static int
sfvmStoragePoolDestroy(virStoragePoolPtr pool)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    int ret = -1;
    virObjectEvent *event = NULL;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, pool->name)))
        return -1;
    def = virStoragePoolObjGetDef(obj);

    virStoragePoolObjSetActive(obj, false);

    if (def->source.adapter.type == VIR_STORAGE_ADAPTER_TYPE_FC_HOST) {
        if (sfvmDestroyVport(privconn,
                             def->source.adapter.data.fchost.wwnn,
                             def->source.adapter.data.fchost.wwpn) < 0)
            goto cleanup;
    }

    event = virStoragePoolEventLifecycleNew(def->name,
                                            def->uuid,
                                            VIR_STORAGE_POOL_EVENT_STOPPED,
                                            0);

    if (!(virStoragePoolObjGetConfigFile(obj)))
        virStoragePoolObjRemove(privconn->pools, obj);

    ret = 0;

 cleanup:
    virObjectEventStateQueue(privconn->eventState, event);
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStoragePoolDelete(virStoragePoolPtr pool,
                      unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virObjectEvent *event = NULL;

    virCheckFlags(0, -1);

    if (!(obj = sfvmStoragePoolObjFindInactiveByName(privconn, pool->name)))
        return -1;

    event = virStoragePoolEventLifecycleNew(pool->name, pool->uuid,
                                            VIR_STORAGE_POOL_EVENT_DELETED,
                                            0);

    virObjectEventStateQueue(privconn->eventState, event);

    virStoragePoolObjEndAPI(&obj);
    return 0;
}


static int
sfvmStoragePoolRefresh(virStoragePoolPtr pool,
                       unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virObjectEvent *event = NULL;

    virCheckFlags(0, -1);

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, pool->name)))
        return -1;

    event = virStoragePoolEventRefreshNew(pool->name, pool->uuid);

    virObjectEventStateQueue(privconn->eventState, event);
    virStoragePoolObjEndAPI(&obj);
    return 0;
}


static int
sfvmStoragePoolGetInfo(virStoragePoolPtr pool,
                       virStoragePoolInfoPtr info)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;

    if (!(obj = sfvmStoragePoolObjFindByName(privconn, pool->name)))
        return -1;
    def = virStoragePoolObjGetDef(obj);

    memset(info, 0, sizeof(virStoragePoolInfo));
    if (virStoragePoolObjIsActive(obj))
        info->state = VIR_STORAGE_POOL_RUNNING;
    else
        info->state = VIR_STORAGE_POOL_INACTIVE;
    info->capacity = def->capacity;
    info->allocation = def->allocation;
    info->available = def->available;

    virStoragePoolObjEndAPI(&obj);
    return 0;
}


static char *
sfvmStoragePoolGetXMLDesc(virStoragePoolPtr pool,
                          unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    char *ret = NULL;

    virCheckFlags(0, NULL);

    if (!(obj = sfvmStoragePoolObjFindByName(privconn, pool->name)))
        return NULL;

    ret = virStoragePoolDefFormat(virStoragePoolObjGetDef(obj));

    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStoragePoolGetAutostart(virStoragePoolPtr pool,
                            int *autostart)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;

    if (!(obj = sfvmStoragePoolObjFindByName(privconn, pool->name)))
        return -1;

    if (!virStoragePoolObjGetConfigFile(obj))
        *autostart = 0;
    else
        *autostart = virStoragePoolObjIsAutostart(obj) ? 1 : 0;

    virStoragePoolObjEndAPI(&obj);
    return 0;
}


static int
sfvmStoragePoolSetAutostart(virStoragePoolPtr pool,
                            int autostart)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    bool new_autostart = (autostart != 0);
    int ret = -1;

    if (!(obj = sfvmStoragePoolObjFindByName(privconn, pool->name)))
        return -1;

    if (!virStoragePoolObjGetConfigFile(obj)) {
        virReportError(VIR_ERR_INVALID_ARG,
                       "%s", _("pool has no config file"));
        goto cleanup;
    }

    virStoragePoolObjSetAutostart(obj, new_autostart);
    ret = 0;

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStoragePoolNumOfVolumes(virStoragePoolPtr pool)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    int ret = -1;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, pool->name)))
        return -1;

    ret = virStoragePoolObjNumOfVolumes(obj, pool->conn, NULL);

    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStoragePoolListVolumes(virStoragePoolPtr pool,
                           char **const names,
                           int maxnames)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    int n = -1;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, pool->name)))
        return -1;

    n = virStoragePoolObjVolumeGetNames(obj, pool->conn, NULL, names, maxnames);

    virStoragePoolObjEndAPI(&obj);
    return n;
}


static int
sfvmStoragePoolListAllVolumes(virStoragePoolPtr pool,
                              virStorageVolPtr **vols,
                              unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(obj = sfvmStoragePoolObjFindByUUID(privconn, pool->uuid)))
        return -1;

    if (!virStoragePoolObjIsActive(obj)) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("storage pool is not active"));
        goto cleanup;
    }

    ret = virStoragePoolObjVolumeListExport(pool->conn, obj, vols, NULL);

 cleanup:
    virStoragePoolObjEndAPI(&obj);

    return ret;
}


static virStorageVolDef *
sfvmStorageVolDefFindByName(virStoragePoolObj *obj,
                            const char *name)
{
    virStorageVolDef *privvol;

    if (!(privvol = virStorageVolDefFindByName(obj, name))) {
        virReportError(VIR_ERR_NO_STORAGE_VOL,
                       _("no storage vol with matching name '%s'"), name);
    }

    return privvol;
}


static virStorageVolPtr
sfvmStorageVolLookupByName(virStoragePoolPtr pool,
                           const char *name)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    virStorageVolDef *privvol;
    virStorageVolPtr ret = NULL;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, pool->name)))
        return NULL;
    def = virStoragePoolObjGetDef(obj);

    if (!(privvol = sfvmStorageVolDefFindByName(obj, name)))
        goto cleanup;

    ret = virGetStorageVol(pool->conn, def->name,
                           privvol->name, privvol->key,
                           NULL, NULL);

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


struct storageVolLookupData {
    const char *key;
    const char *path;
    virStorageVolDef *voldef;
};

static bool
sfvmStorageVolLookupByKeyCallback(virStoragePoolObj *obj,
                                  const void *opaque)
{
    struct storageVolLookupData *data = (struct storageVolLookupData *)opaque;

    if (virStoragePoolObjIsActive(obj))
        data->voldef = virStorageVolDefFindByKey(obj, data->key);

    return !!data->voldef;
}


static virStorageVolPtr
sfvmStorageVolLookupByKey(virConnectPtr conn,
                          const char *key)
{
    sfvmDriver *privconn = conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    struct storageVolLookupData data = {
        .key = key, .voldef = NULL };
    virStorageVolPtr vol = NULL;

    virObjectLock(privconn);
    if ((obj = virStoragePoolObjListSearch(privconn->pools,
                                           sfvmStorageVolLookupByKeyCallback,
                                           &data)) && data.voldef) {
        def = virStoragePoolObjGetDef(obj);
        vol = virGetStorageVol(conn, def->name,
                               data.voldef->name, data.voldef->key,
                               NULL, NULL);
        virStoragePoolObjEndAPI(&obj);
    }
    virObjectUnlock(privconn);

    if (!vol)
        virReportError(VIR_ERR_NO_STORAGE_VOL,
                       _("no storage vol with matching key '%s'"), key);

    return vol;
}


static bool
sfvmStorageVolLookupByPathCallback(virStoragePoolObj *obj,
                                   const void *opaque)
{
    struct storageVolLookupData *data = (struct storageVolLookupData *)opaque;

    if (virStoragePoolObjIsActive(obj))
        data->voldef = virStorageVolDefFindByPath(obj, data->path);

    return !!data->voldef;
}


static virStorageVolPtr
sfvmStorageVolLookupByPath(virConnectPtr conn,
                           const char *path)
{
    sfvmDriver *privconn = conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    struct storageVolLookupData data = {
        .path = path, .voldef = NULL };
    virStorageVolPtr vol = NULL;

    virObjectLock(privconn);
    if ((obj = virStoragePoolObjListSearch(privconn->pools,
                                           sfvmStorageVolLookupByPathCallback,
                                           &data)) && data.voldef) {
        def = virStoragePoolObjGetDef(obj);
        vol = virGetStorageVol(conn, def->name,
                               data.voldef->name, data.voldef->key,
                               NULL, NULL);
        virStoragePoolObjEndAPI(&obj);
    }
    virObjectUnlock(privconn);

    if (!vol)
        virReportError(VIR_ERR_NO_STORAGE_VOL,
                       _("no storage vol with matching path '%s'"), path);

    return vol;
}


static virStorageVolPtr
sfvmStorageVolCreateXML(virStoragePoolPtr pool,
                        const char *xmldesc,
                        unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    virStorageVolPtr ret = NULL;
    g_autoptr(virStorageVolDef) privvol = NULL;
    unsigned int parseFlags = 0;

    virCheckFlags(VIR_STORAGE_VOL_CREATE_VALIDATE, NULL);

    if (flags & VIR_STORAGE_VOL_CREATE_VALIDATE)
        parseFlags |= VIR_VOL_XML_PARSE_VALIDATE;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, pool->name)))
        return NULL;
    def = virStoragePoolObjGetDef(obj);

    privvol = virStorageVolDefParse(def, xmldesc, NULL, parseFlags);
    if (privvol == NULL)
        goto cleanup;

    if (virStorageVolDefFindByName(obj, privvol->name)) {
        virReportError(VIR_ERR_OPERATION_FAILED,
                       "%s", _("storage vol already exists"));
        goto cleanup;
    }

    /* Make sure enough space */
    if ((def->allocation + privvol->target.allocation) >
         def->capacity) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("Not enough free space in pool for volume '%s'"),
                       privvol->name);
        goto cleanup;
    }

    privvol->target.path = g_strdup_printf("%s/%s", def->target.path,
                                           privvol->name);

    privvol->key = g_strdup(privvol->target.path);
    if (virStoragePoolObjAddVol(obj, privvol) < 0)
        goto cleanup;

    def->allocation += privvol->target.allocation;
    def->available = (def->capacity - def->allocation);

    ret = virGetStorageVol(pool->conn, def->name,
                           privvol->name, privvol->key,
                           NULL, NULL);
    privvol = NULL;

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static virStorageVolPtr
sfvmStorageVolCreateXMLFrom(virStoragePoolPtr pool,
                            const char *xmldesc,
                            virStorageVolPtr clonevol,
                            unsigned int flags)
{
    sfvmDriver *privconn = pool->conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    virStorageVolDef *origvol = NULL;
    virStorageVolPtr ret = NULL;
    g_autoptr(virStorageVolDef) privvol = NULL;
    unsigned int parseFlags = 0;

    virCheckFlags(VIR_STORAGE_VOL_CREATE_VALIDATE, NULL);

    if (flags & VIR_STORAGE_VOL_CREATE_VALIDATE)
        parseFlags |= VIR_VOL_XML_PARSE_VALIDATE;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, pool->name)))
        return NULL;
    def = virStoragePoolObjGetDef(obj);

    privvol = virStorageVolDefParse(def, xmldesc, NULL, parseFlags);
    if (privvol == NULL)
        goto cleanup;

    if (virStorageVolDefFindByName(obj, privvol->name)) {
        virReportError(VIR_ERR_OPERATION_FAILED,
                       "%s", _("storage vol already exists"));
        goto cleanup;
    }

    origvol = virStorageVolDefFindByName(obj, clonevol->name);
    if (!origvol) {
        virReportError(VIR_ERR_NO_STORAGE_VOL,
                       _("no storage vol with matching name '%s'"),
                       clonevol->name);
        goto cleanup;
    }

    /* Make sure enough space */
    if ((def->allocation + privvol->target.allocation) > def->capacity) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("Not enough free space in pool for volume '%s'"),
                       privvol->name);
        goto cleanup;
    }
    def->available = (def->capacity - def->allocation);

    privvol->target.path = g_strdup_printf("%s/%s", def->target.path,
                                           privvol->name);

    privvol->key = g_strdup(privvol->target.path);
    if (virStoragePoolObjAddVol(obj, privvol) < 0)
        goto cleanup;

    def->allocation += privvol->target.allocation;
    def->available = (def->capacity - def->allocation);

    ret = virGetStorageVol(pool->conn, def->name,
                           privvol->name, privvol->key,
                           NULL, NULL);
    privvol = NULL;

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStorageVolDelete(virStorageVolPtr vol,
                     unsigned int flags)
{
    sfvmDriver *privconn = vol->conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    virStorageVolDef *privvol;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, vol->pool)))
        return -1;
    def = virStoragePoolObjGetDef(obj);

    if (!(privvol = sfvmStorageVolDefFindByName(obj, vol->name)))
        goto cleanup;

    def->allocation -= privvol->target.allocation;
    def->available = (def->capacity - def->allocation);

    virStoragePoolObjRemoveVol(obj, privvol);

    ret = 0;

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static int
sfvmStorageVolumeTypeForPool(int pooltype)
{
    switch ((virStoragePoolType) pooltype) {
    case VIR_STORAGE_POOL_DIR:
    case VIR_STORAGE_POOL_FS:
    case VIR_STORAGE_POOL_NETFS:
    case VIR_STORAGE_POOL_VSTORAGE:
        return VIR_STORAGE_VOL_FILE;
    case VIR_STORAGE_POOL_SHEEPDOG:
    case VIR_STORAGE_POOL_ISCSI_DIRECT:
    case VIR_STORAGE_POOL_GLUSTER:
    case VIR_STORAGE_POOL_RBD:
        return VIR_STORAGE_VOL_NETWORK;
    case VIR_STORAGE_POOL_LOGICAL:
    case VIR_STORAGE_POOL_DISK:
    case VIR_STORAGE_POOL_MPATH:
    case VIR_STORAGE_POOL_ISCSI:
    case VIR_STORAGE_POOL_SCSI:
    case VIR_STORAGE_POOL_ZFS:
        return VIR_STORAGE_VOL_BLOCK;
    case VIR_STORAGE_POOL_LAST:
    default:
        virReportEnumRangeError(virStoragePoolType, pooltype);
        return -1;
    }
}


static int
sfvmStorageVolGetInfo(virStorageVolPtr vol,
                      virStorageVolInfoPtr info)
{
    sfvmDriver *privconn = vol->conn->privateData;
    virStoragePoolObj *obj;
    virStoragePoolDef *def;
    virStorageVolDef *privvol;
    int ret = -1;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, vol->pool)))
        return -1;
    def = virStoragePoolObjGetDef(obj);

    if (!(privvol = sfvmStorageVolDefFindByName(obj, vol->name)))
        goto cleanup;

    memset(info, 0, sizeof(*info));
    if ((info->type = sfvmStorageVolumeTypeForPool(def->type)) < 0)
        goto cleanup;
    info->capacity = privvol->target.capacity;
    info->allocation = privvol->target.allocation;
    ret = 0;

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static char *
sfvmStorageVolGetXMLDesc(virStorageVolPtr vol,
                         unsigned int flags)
{
    sfvmDriver *privconn = vol->conn->privateData;
    virStoragePoolObj *obj;
    virStorageVolDef *privvol;
    char *ret = NULL;

    virCheckFlags(0, NULL);

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, vol->pool)))
        return NULL;

    if (!(privvol = sfvmStorageVolDefFindByName(obj, vol->name)))
        goto cleanup;

    ret = virStorageVolDefFormat(virStoragePoolObjGetDef(obj), privvol);

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


static char *
sfvmStorageVolGetPath(virStorageVolPtr vol)
{
    sfvmDriver *privconn = vol->conn->privateData;
    virStoragePoolObj *obj;
    virStorageVolDef *privvol;
    char *ret = NULL;

    if (!(obj = sfvmStoragePoolObjFindActiveByName(privconn, vol->pool)))
        return NULL;

    if (!(privvol = sfvmStorageVolDefFindByName(obj, vol->name)))
        goto cleanup;

    ret = g_strdup(privvol->target.path);

 cleanup:
    virStoragePoolObjEndAPI(&obj);
    return ret;
}


/* Node device implementations */

static virNodeDeviceObj *
sfvmNodeDeviceObjFindByName(sfvmDriver *driver,
                            const char *name)
{
    virNodeDeviceObj *obj;

    if (!(obj = virNodeDeviceObjListFindByName(driver->devs, name)))
        virReportError(VIR_ERR_NO_NODE_DEVICE,
                       _("no node device with matching name '%s'"),
                       name);

    return obj;
}


static int
sfvmNodeNumOfDevices(virConnectPtr conn,
                     const char *cap,
                     unsigned int flags)
{
    sfvmDriver *driver = conn->privateData;

    virCheckFlags(0, -1);

    return virNodeDeviceObjListNumOfDevices(driver->devs, conn, cap, NULL);
}


static int
sfvmNodeListDevices(virConnectPtr conn,
                    const char *cap,
                    char **const names,
                    int maxnames,
                    unsigned int flags)
{
    sfvmDriver *driver = conn->privateData;

    virCheckFlags(0, -1);

    return virNodeDeviceObjListGetNames(driver->devs, conn, NULL,
                                        cap, names, maxnames);
}

static int
sfvmConnectListAllNodeDevices(virConnectPtr conn,
                              virNodeDevicePtr **devices,
                              unsigned int flags)
{
    sfvmDriver *driver = conn->privateData;

    virCheckFlags(VIR_CONNECT_LIST_NODE_DEVICES_FILTERS_CAP, -1);

    return virNodeDeviceObjListExport(conn, driver->devs, devices,
                                      NULL, flags);
}

static virNodeDevicePtr
sfvmNodeDeviceLookupByName(virConnectPtr conn, const char *name)
{
    sfvmDriver *driver = conn->privateData;
    virNodeDeviceObj *obj;
    virNodeDeviceDef *def;
    virNodeDevicePtr ret = NULL;

    if (!(obj = sfvmNodeDeviceObjFindByName(driver, name)))
        return NULL;
    def = virNodeDeviceObjGetDef(obj);

    if ((ret = virGetNodeDevice(conn, name)))
        ret->parentName = g_strdup(def->parent);

    virNodeDeviceObjEndAPI(&obj);
    return ret;
}

static char *
sfvmNodeDeviceGetXMLDesc(virNodeDevicePtr dev,
                         unsigned int flags)
{
    sfvmDriver *driver = dev->conn->privateData;
    virNodeDeviceObj *obj;
    char *ret = NULL;

    virCheckFlags(0, NULL);

    if (!(obj = sfvmNodeDeviceObjFindByName(driver, dev->name)))
        return NULL;

    ret = virNodeDeviceDefFormat(virNodeDeviceObjGetDef(obj));

    virNodeDeviceObjEndAPI(&obj);
    return ret;
}

static char *
sfvmNodeDeviceGetParent(virNodeDevicePtr dev)
{
    sfvmDriver *driver = dev->conn->privateData;
    virNodeDeviceObj *obj;
    virNodeDeviceDef *def;
    char *ret = NULL;

    if (!(obj = sfvmNodeDeviceObjFindByName(driver, dev->name)))
        return NULL;
    def = virNodeDeviceObjGetDef(obj);

    if (def->parent) {
        ret = g_strdup(def->parent);
    } else {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       "%s", _("no parent for this device"));
    }

    virNodeDeviceObjEndAPI(&obj);
    return ret;
}


static int
sfvmNodeDeviceNumOfCaps(virNodeDevicePtr dev)
{
    sfvmDriver *driver = dev->conn->privateData;
    virNodeDeviceObj *obj;
    virNodeDeviceDef *def;
    virNodeDevCapsDef *caps;
    int ncaps = 0;

    if (!(obj = sfvmNodeDeviceObjFindByName(driver, dev->name)))
        return -1;
    def = virNodeDeviceObjGetDef(obj);

    for (caps = def->caps; caps; caps = caps->next)
        ++ncaps;

    virNodeDeviceObjEndAPI(&obj);
    return ncaps;
}


static int
sfvmNodeDeviceListCaps(virNodeDevicePtr dev, char **const names, int maxnames)
{
    sfvmDriver *driver = dev->conn->privateData;
    virNodeDeviceObj *obj;
    virNodeDeviceDef *def;
    virNodeDevCapsDef *caps;
    int ncaps = 0;

    if (!(obj = sfvmNodeDeviceObjFindByName(driver, dev->name)))
        return -1;
    def = virNodeDeviceObjGetDef(obj);

    for (caps = def->caps; caps && ncaps < maxnames; caps = caps->next) {
        names[ncaps] = g_strdup(virNodeDevCapTypeToString(caps->data.type));
        ncaps++;
    }

    virNodeDeviceObjEndAPI(&obj);
    return ncaps;
}


static virNodeDeviceObj *
sfvmNodeDeviceMockCreateVport(sfvmDriver *driver,
                              const char *wwnn,
                              const char *wwpn)
{
    virNodeDeviceDef *def = NULL;
    virNodeDevCapsDef *caps;
    virNodeDeviceObj *obj = NULL;
    virNodeDeviceObj *objcopy = NULL;
    virNodeDeviceDef *objdef;
    virObjectEvent *event = NULL;
    g_autofree char *xml = NULL;

    /* In the real code, we'd call virVHBAManageVport which would take the
     * wwnn/wwpn from the input XML in order to call the "vport_create"
     * function for the parent. That in turn would set off a sequence of
     * events resulting in the creation of a vHBA scsi_hostN in the
     * node device objects list using the "next" host number with the
     * wwnn/wwpn from the input XML. The following will mock this by
     * using the scsi_host11 definition, changing the name and the
     * scsi_host capability fields before calling virNodeDeviceAssignDef
     * to add the def to the node device objects list. */
    if (!(objcopy = virNodeDeviceObjListFindByName(driver->devs,
                                                   "scsi_host11")))
        goto cleanup;

    xml = virNodeDeviceDefFormat(virNodeDeviceObjGetDef(objcopy));
    virNodeDeviceObjEndAPI(&objcopy);
    if (!xml)
        goto cleanup;

    if (!(def = virNodeDeviceDefParse(xml, NULL, EXISTING_DEVICE, NULL, NULL, NULL, false)))
        goto cleanup;

    VIR_FREE(def->name);
    def->name = g_strdup("scsi_host12");

    /* Find the 'scsi_host' cap and alter the host # and unique_id and
     * then for the 'fc_host' capability modify the wwnn/wwpn to be that
     * of the input XML. */
    caps = def->caps;
    while (caps) {
        if (caps->data.type != VIR_NODE_DEV_CAP_SCSI_HOST)
            continue;

        /* For the "fc_host" cap - change the wwnn/wwpn to match the input */
        if (caps->data.scsi_host.flags & VIR_NODE_DEV_CAP_FLAG_HBA_FC_HOST) {
            VIR_FREE(caps->data.scsi_host.wwnn);
            VIR_FREE(caps->data.scsi_host.wwpn);
            caps->data.scsi_host.wwnn = g_strdup(wwnn);
            caps->data.scsi_host.wwpn = g_strdup(wwpn);
        } else {
            /* For the "scsi_host" cap, increment our host and unique_id to
             * give the appearance that something new was created - then add
             * that to the node device driver */
            caps->data.scsi_host.host++;
            caps->data.scsi_host.unique_id++;
        }
        caps = caps->next;
    }

    if (!(obj = virNodeDeviceObjListAssignDef(driver->devs, def)))
        goto cleanup;
    virNodeDeviceObjSetSkipUpdateCaps(obj, true);
    def = NULL;
    objdef = virNodeDeviceObjGetDef(obj);

    event = virNodeDeviceEventLifecycleNew(objdef->name,
                                           VIR_NODE_DEVICE_EVENT_CREATED,
                                           0);
    virObjectEventStateQueue(driver->eventState, event);

 cleanup:
    virNodeDeviceDefFree(def);
    return obj;
}


static virNodeDevicePtr
sfvmNodeDeviceCreateXML(virConnectPtr conn,
                        const char *xmlDesc,
                        unsigned int flags)
{
    sfvmDriver *driver = conn->privateData;
    virNodeDeviceDef *def = NULL;
    virNodeDevicePtr dev = NULL, ret = NULL;
    virNodeDeviceObj *obj = NULL;
    virNodeDeviceDef *objdef;
    g_autofree char *wwnn = NULL;
    g_autofree char *wwpn = NULL;
    bool validate = flags & VIR_NODE_DEVICE_CREATE_XML_VALIDATE;

    virCheckFlags(VIR_NODE_DEVICE_CREATE_XML_VALIDATE, NULL);

    if (!(def = virNodeDeviceDefParse(xmlDesc, NULL, CREATE_DEVICE, NULL, NULL,
                                      NULL, validate)))
        goto cleanup;

    /* We run this simply for validation - it essentially validates that
     * the input XML either has a wwnn/wwpn or virNodeDevCapSCSIHostParseXML
     * generated a wwnn/wwpn */
    if (virNodeDeviceGetWWNs(def, &wwnn, &wwpn) < 0)
        goto cleanup;

    /* Unlike the "real" code we don't need the parent_host in order to
     * call virVHBAManageVport, but still let's make sure the code finds
     * something valid and no one messed up the mock environment. */
    if (virNodeDeviceObjListGetParentHost(driver->devs, def) < 0)
        goto cleanup;

    /* In the real code, we'd call virVHBAManageVport followed by
     * find_new_device, but we cannot do that here since we're not
     * mocking udev. The mock routine will copy an existing vHBA and
     * rename a few fields to mock that. So in order to allow that to
     * work properly, we need to drop our lock */
    if (!(obj = sfvmNodeDeviceMockCreateVport(driver, wwnn, wwpn)))
        goto cleanup;
    objdef = virNodeDeviceObjGetDef(obj);

    if (!(dev = virGetNodeDevice(conn, objdef->name)))
        goto cleanup;

    VIR_FREE(dev->parentName);
    dev->parentName = g_strdup(def->parent);

    ret = g_steal_pointer(&dev);

 cleanup:
    virNodeDeviceObjEndAPI(&obj);
    virNodeDeviceDefFree(def);
    virObjectUnref(dev);
    return ret;
}

static int
sfvmNodeDeviceDestroy(virNodeDevicePtr dev)
{
    int ret = 0;
    sfvmDriver *driver = dev->conn->privateData;
    virNodeDeviceObj *obj = NULL;
    virNodeDeviceObj *parentobj = NULL;
    virNodeDeviceDef *def;
    virObjectEvent *event = NULL;
    g_autofree char *wwnn = NULL;
    g_autofree char *wwpn = NULL;

    if (!(obj = sfvmNodeDeviceObjFindByName(driver, dev->name)))
        return -1;
    def = virNodeDeviceObjGetDef(obj);

    if (virNodeDeviceGetWWNs(def, &wwnn, &wwpn) == -1)
        goto cleanup;

    /* Unlike the real code we cannot run into the udevAddOneDevice race
     * which would replace obj->def, so no need to save off the parent,
     * but do need to drop the @obj lock so that the FindByName code doesn't
     * deadlock on ourselves */
    virObjectUnlock(obj);

    /* We do this just for basic validation and throw away the parentobj
     * since there's no vport_delete to be run */
    if (!(parentobj = virNodeDeviceObjListFindByName(driver->devs,
                                                     def->parent))) {
        virReportError(VIR_ERR_INTERNAL_ERROR,
                       _("cannot find parent '%s' definition"), def->parent);
        virObjectLock(obj);
        goto cleanup;
    }
    virNodeDeviceObjEndAPI(&parentobj);

    event = virNodeDeviceEventLifecycleNew(dev->name,
                                           VIR_NODE_DEVICE_EVENT_DELETED,
                                           0);

    virObjectLock(obj);
    virNodeDeviceObjListRemove(driver->devs, obj);

 cleanup:
    virNodeDeviceObjEndAPI(&obj);
    virObjectEventStateQueue(driver->eventState, event);
    return ret;
}


/* Domain event implementations */
static int
sfvmConnectDomainEventRegister(virConnectPtr conn,
                               virConnectDomainEventCallback callback,
                               void *opaque,
                               virFreeCallback freecb)
{
    sfvmDriver *driver = conn->privateData;
    int ret = 0;

    if (virDomainEventStateRegister(conn, driver->eventState,
                                    callback, opaque, freecb) < 0)
        ret = -1;

    return ret;
}


static int
sfvmConnectDomainEventDeregister(virConnectPtr conn,
                                 virConnectDomainEventCallback callback)
{
    sfvmDriver *driver = conn->privateData;
    int ret = 0;

    if (virDomainEventStateDeregister(conn, driver->eventState,
                                      callback) < 0)
        ret = -1;

    return ret;
}


static int
sfvmConnectDomainEventRegisterAny(virConnectPtr conn,
                                  virDomainPtr dom,
                                  int eventID,
                                  virConnectDomainEventGenericCallback callback,
                                  void *opaque,
                                  virFreeCallback freecb)
{
    sfvmDriver *driver = conn->privateData;
    int ret;

    if (virDomainEventStateRegisterID(conn, driver->eventState,
                                      dom, eventID,
                                      callback, opaque, freecb, &ret) < 0)
        ret = -1;

    return ret;
}

static int
sfvmConnectDomainEventDeregisterAny(virConnectPtr conn,
                                    int callbackID)
{
    sfvmDriver *driver = conn->privateData;
    int ret = 0;

    if (virObjectEventStateDeregisterID(conn, driver->eventState,
                                        callbackID, true) < 0)
        ret = -1;

    return ret;
}


static int
sfvmConnectNetworkEventRegisterAny(virConnectPtr conn,
                                   virNetworkPtr net,
                                   int eventID,
                                   virConnectNetworkEventGenericCallback callback,
                                   void *opaque,
                                   virFreeCallback freecb)
{
    sfvmDriver *driver = conn->privateData;
    int ret;

    if (virNetworkEventStateRegisterID(conn, driver->eventState,
                                       net, eventID, callback,
                                       opaque, freecb, &ret) < 0)
        ret = -1;

    return ret;
}

static int
sfvmConnectNetworkEventDeregisterAny(virConnectPtr conn,
                                     int callbackID)
{
    sfvmDriver *driver = conn->privateData;
    int ret = 0;

    if (virObjectEventStateDeregisterID(conn, driver->eventState,
                                        callbackID, true) < 0)
        ret = -1;

    return ret;
}

static int
sfvmConnectStoragePoolEventRegisterAny(virConnectPtr conn,
                                       virStoragePoolPtr pool,
                                       int eventID,
                                       virConnectStoragePoolEventGenericCallback callback,
                                       void *opaque,
                                       virFreeCallback freecb)
{
    sfvmDriver *driver = conn->privateData;
    int ret;

    if (virStoragePoolEventStateRegisterID(conn, driver->eventState,
                                           pool, eventID, callback,
                                           opaque, freecb, &ret) < 0)
        ret = -1;

    return ret;
}

static int
sfvmConnectStoragePoolEventDeregisterAny(virConnectPtr conn,
                                         int callbackID)
{
    sfvmDriver *driver = conn->privateData;
    int ret = 0;

    if (virObjectEventStateDeregisterID(conn, driver->eventState,
                                        callbackID, true) < 0)
        ret = -1;

    return ret;
}

static int
sfvmConnectNodeDeviceEventRegisterAny(virConnectPtr conn,
                                      virNodeDevicePtr dev,
                                      int eventID,
                                      virConnectNodeDeviceEventGenericCallback callback,
                                      void *opaque,
                                      virFreeCallback freecb)
{
    sfvmDriver *driver = conn->privateData;
    int ret;

    if (virNodeDeviceEventStateRegisterID(conn, driver->eventState,
                                          dev, eventID, callback,
                                          opaque, freecb, &ret) < 0)
        ret = -1;

    return ret;
}

static int
sfvmConnectNodeDeviceEventDeregisterAny(virConnectPtr conn,
                                        int callbackID)
{
    sfvmDriver *driver = conn->privateData;
    int ret = 0;

    if (virObjectEventStateDeregisterID(conn, driver->eventState,
                                        callbackID, true) < 0)
        ret = -1;

    return ret;
}

static int sfvmConnectListAllDomains(virConnectPtr conn,
                                     virDomainPtr **domains,
                                     unsigned int flags)
{
    sfvmDriver *privconn = conn->privateData;

    virCheckFlags(VIR_CONNECT_LIST_DOMAINS_FILTERS_ALL, -1);

    return virDomainObjListExport(privconn->domains, conn, domains,
                                  NULL, flags);
}

static int
sfvmNodeGetCPUMap(virConnectPtr conn G_GNUC_UNUSED,
                  unsigned char **cpumap,
                  unsigned int *online,
                  unsigned int flags)
{
    virCheckFlags(0, -1);

    if (cpumap) {
        *cpumap = g_new0(unsigned char, 1);
        *cpumap[0] = 0x15;
    }

    if (online)
        *online = 3;

    return  8;
}

static char *
sfvmDomainScreenshot(virDomainPtr dom G_GNUC_UNUSED,
                     virStreamPtr st,
                     unsigned int screen G_GNUC_UNUSED,
                     unsigned int flags)
{
    char *ret = NULL;

    virCheckFlags(0, NULL);

    ret = g_strdup("image/png");

    if (virFDStreamOpenFile(st, PKGDATADIR "/sfvm-screenshot.png", 0, 0, O_RDONLY) < 0)
        VIR_FREE(ret);

    return ret;
}


static int
sfvmDomainInjectNMI(virDomainPtr domain,
                    unsigned int flags)
{
    virDomainObj *vm = NULL;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    /* do nothing */
    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSendKey(virDomainPtr domain,
                  unsigned int codeset,
                  unsigned int holdtime G_GNUC_UNUSED,
                  unsigned int *keycodes,
                  int nkeycodes,
                  unsigned int flags)
{
    int ret = -1;
    size_t i;
    virDomainObj *vm = NULL;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    for (i = 0; i < nkeycodes; i++) {
        if (virKeycodeValueTranslate(codeset, codeset, keycodes[i]) < 0) {
            virReportError(VIR_ERR_INTERNAL_ERROR,
                           _("invalid keycode %u of %s codeset"),
                           keycodes[i],
                           virKeycodeSetTypeToString(codeset));
            goto cleanup;
        }
    }

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmConnectGetCPUModelNames(virConnectPtr conn G_GNUC_UNUSED,
                            const char *archName,
                            char ***models,
                            unsigned int flags)
{
    virArch arch;

    virCheckFlags(0, -1);

    if (!(arch = virArchFromString(archName))) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("cannot find architecture %s"),
                       archName);
        return -1;
    }

    return virCPUGetModels(arch, models);
}

static int
sfvmDomainManagedSave(virDomainPtr dom, unsigned int flags)
{
    sfvmDriver *privconn = dom->conn->privateData;
    virDomainObj *vm = NULL;
    virObjectEvent *event = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_SAVE_BYPASS_CACHE |
                  VIR_DOMAIN_SAVE_RUNNING |
                  VIR_DOMAIN_SAVE_PAUSED, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    if (!vm->persistent) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("cannot do managed save for transient domain"));
        goto cleanup;
    }

    sfvmDomainShutdownState(dom, vm, VIR_DOMAIN_SHUTOFF_SAVED);
    event = virDomainEventLifecycleNewFromObj(vm,
                                     VIR_DOMAIN_EVENT_STOPPED,
                                     VIR_DOMAIN_EVENT_STOPPED_SAVED);
    vm->hasManagedSave = true;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    virObjectEventStateQueue(privconn->eventState, event);

    return ret;
}


static int
sfvmDomainHasManagedSaveImage(virDomainPtr dom, unsigned int flags)
{
    virDomainObj *vm;
    int ret;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    ret = vm->hasManagedSave;

    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainManagedSaveRemove(virDomainPtr dom, unsigned int flags)
{
    virDomainObj *vm;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    vm->hasManagedSave = false;

    virDomainObjEndAPI(&vm);
    return 0;
}


static int
sfvmDomainMemoryStats(virDomainPtr dom,
                      virDomainMemoryStatPtr stats,
                      unsigned int nr_stats,
                      unsigned int flags)
{
    virDomainObj *vm = NULL;
    int cur_memory;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    cur_memory = vm->def->mem.cur_balloon;
    ret = 0;

#define STATS_SET_PARAM(name, value) \
    if (ret < nr_stats) { \
        stats[ret].tag = name; \
        stats[ret].val = value; \
        ret++; \
    }

    if (virDomainDefHasMemballoon(vm->def)) {
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_ACTUAL_BALLOON, cur_memory);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_SWAP_IN, 0);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_SWAP_OUT, 0);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_MAJOR_FAULT, 0);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_MINOR_FAULT, 0);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_UNUSED, cur_memory / 2);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_AVAILABLE, cur_memory);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_USABLE, cur_memory / 2);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_LAST_UPDATE, 627319920);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_DISK_CACHES, cur_memory / 8);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_HUGETLB_PGALLOC, 0);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_HUGETLB_PGFAIL, 0);
        STATS_SET_PARAM(VIR_DOMAIN_MEMORY_STAT_RSS, cur_memory / 2);
    }

#undef STATS_SET_PARAM

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainMemoryPeek(virDomainPtr dom,
                     unsigned long long start,
                     size_t size,
                     void *buffer,
                     unsigned int flags)
{
    int ret = -1;
    size_t i;
    unsigned char b = start;
    virDomainObj *vm = NULL;

    virCheckFlags(VIR_MEMORY_VIRTUAL | VIR_MEMORY_PHYSICAL, -1);

    if (flags != VIR_MEMORY_VIRTUAL && flags != VIR_MEMORY_PHYSICAL) {
        virReportError(VIR_ERR_INVALID_ARG,
                       "%s", _("flags parameter must be VIR_MEMORY_VIRTUAL or VIR_MEMORY_PHYSICAL"));
        goto cleanup;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (virDomainObjCheckActive(vm) < 0)
        goto cleanup;

    for (i = 0; i < size; i++)
        ((unsigned char *) buffer)[i] = b++;

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainGetBlockInfo(virDomainPtr dom,
                       const char *path,
                       virDomainBlockInfoPtr info,
                       unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDiskDef *disk;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (!(disk = virDomainDiskByName(vm->def, path, false))) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("invalid path %s not assigned to domain"), path);
        goto cleanup;
    }

    if (virStorageSourceIsEmpty(disk->src)) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("disk '%s' does not currently have a source assigned"),
                       path);
        goto cleanup;
    }

    info->capacity = 1099506450432;
    info->allocation = 1099511627776;
    info->physical = 1099511627776;

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static void
sfvmDomainModifyLifecycleAction(virDomainDef *def,
                                virDomainLifecycle type,
                                virDomainLifecycleAction action)
{
    switch (type) {
    case VIR_DOMAIN_LIFECYCLE_POWEROFF:
        def->onPoweroff = action;
        break;
    case VIR_DOMAIN_LIFECYCLE_REBOOT:
        def->onReboot = action;
        break;
    case VIR_DOMAIN_LIFECYCLE_CRASH:
        def->onCrash = action;
        break;
    case VIR_DOMAIN_LIFECYCLE_LAST:
        break;
    }
}


static int
sfvmDomainSetLifecycleAction(virDomainPtr dom,
                             unsigned int type,
                             unsigned int action,
                             unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainDef *def = NULL;
    virDomainDef *persistentDef = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (!virDomainDefLifecycleActionAllowed(type, action))
        return -1;

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    if (virDomainObjGetDefs(vm, flags, &def, &persistentDef) < 0)
        goto cleanup;

    if (def)
        sfvmDomainModifyLifecycleAction(def, type, action);

    if (persistentDef)
        sfvmDomainModifyLifecycleAction(persistentDef, type, action);

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


/*
 * Snapshot APIs
 */

static virDomainMomentObj *
sfvmSnapObjFromName(virDomainObj *vm,
                    const char *name)
{
    virDomainMomentObj *snap = NULL;
    snap = virDomainSnapshotFindByName(vm->snapshots, name);
    if (!snap)
        virReportError(VIR_ERR_NO_DOMAIN_SNAPSHOT,
                       _("no domain snapshot with matching name '%s'"),
                       name);
    return snap;
}

static virDomainMomentObj *
sfvmSnapObjFromSnapshot(virDomainObj *vm,
                        virDomainSnapshotPtr snapshot)
{
    return sfvmSnapObjFromName(vm, snapshot->name);
}

static virDomainObj *
sfvmDomObjFromSnapshot(virDomainSnapshotPtr snapshot)
{
    return sfvmDomObjFromDomain(snapshot->domain);
}

static int
sfvmDomainSnapshotNum(virDomainPtr domain, unsigned int flags)
{
    virDomainObj *vm = NULL;
    int n;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_LIST_ROOTS |
                  VIR_DOMAIN_SNAPSHOT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_SNAPSHOT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    n = virDomainSnapshotObjListNum(vm->snapshots, NULL, flags);

    virDomainObjEndAPI(&vm);
    return n;
}

static int
sfvmDomainSnapshotListNames(virDomainPtr domain,
                            char **names,
                            int nameslen,
                            unsigned int flags)
{
    virDomainObj *vm = NULL;
    int n;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_LIST_ROOTS |
                  VIR_DOMAIN_SNAPSHOT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_SNAPSHOT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    n = virDomainSnapshotObjListGetNames(vm->snapshots, NULL, names, nameslen,
                                         flags);

    virDomainObjEndAPI(&vm);
    return n;
}

static int
sfvmDomainListAllSnapshots(virDomainPtr domain,
                           virDomainSnapshotPtr **snaps,
                           unsigned int flags)
{
    virDomainObj *vm = NULL;
    int n;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_LIST_ROOTS |
                  VIR_DOMAIN_SNAPSHOT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_SNAPSHOT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    n = virDomainListSnapshots(vm->snapshots, NULL, domain, snaps, flags);

    virDomainObjEndAPI(&vm);
    return n;
}

static int
sfvmDomainSnapshotListChildrenNames(virDomainSnapshotPtr snapshot,
                                    char **names,
                                    int nameslen,
                                    unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainMomentObj *snap = NULL;
    int n = -1;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_LIST_DESCENDANTS |
                  VIR_DOMAIN_SNAPSHOT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_SNAPSHOT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return -1;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;

    n = virDomainSnapshotObjListGetNames(vm->snapshots, snap, names, nameslen,
                                         flags);

 cleanup:
    virDomainObjEndAPI(&vm);
    return n;
}

static int
sfvmDomainSnapshotNumChildren(virDomainSnapshotPtr snapshot,
                              unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainMomentObj *snap = NULL;
    int n = -1;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_LIST_DESCENDANTS |
                  VIR_DOMAIN_SNAPSHOT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_SNAPSHOT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return -1;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;

    n = virDomainSnapshotObjListNum(vm->snapshots, snap, flags);

 cleanup:
    virDomainObjEndAPI(&vm);
    return n;
}

static int
sfvmDomainSnapshotListAllChildren(virDomainSnapshotPtr snapshot,
                                  virDomainSnapshotPtr **snaps,
                                  unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainMomentObj *snap = NULL;
    int n = -1;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_LIST_DESCENDANTS |
                  VIR_DOMAIN_SNAPSHOT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_SNAPSHOT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return -1;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;

    n = virDomainListSnapshots(vm->snapshots, snap, snapshot->domain, snaps,
                               flags);

 cleanup:
    virDomainObjEndAPI(&vm);
    return n;
}

static virDomainSnapshotPtr
sfvmDomainSnapshotLookupByName(virDomainPtr domain,
                               const char *name,
                               unsigned int flags)
{
    virDomainObj *vm;
    virDomainMomentObj *snap = NULL;
    virDomainSnapshotPtr snapshot = NULL;

    virCheckFlags(0, NULL);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return NULL;

    if (!(snap = sfvmSnapObjFromName(vm, name)))
        goto cleanup;

    snapshot = virGetDomainSnapshot(domain, snap->def->name);

 cleanup:
    virDomainObjEndAPI(&vm);
    return snapshot;
}

static int
sfvmDomainHasCurrentSnapshot(virDomainPtr domain,
                             unsigned int flags)
{
    virDomainObj *vm;
    int ret;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    ret = (virDomainSnapshotGetCurrent(vm->snapshots) != NULL);

    virDomainObjEndAPI(&vm);
    return ret;
}

static virDomainSnapshotPtr
sfvmDomainSnapshotGetParent(virDomainSnapshotPtr snapshot,
                            unsigned int flags)
{
    virDomainObj *vm;
    virDomainMomentObj *snap = NULL;
    virDomainSnapshotPtr parent = NULL;

    virCheckFlags(0, NULL);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return NULL;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;

    if (!snap->def->parent_name) {
        virReportError(VIR_ERR_NO_DOMAIN_SNAPSHOT,
                       _("snapshot '%s' does not have a parent"),
                       snap->def->name);
        goto cleanup;
    }

    parent = virGetDomainSnapshot(snapshot->domain, snap->def->parent_name);

 cleanup:
    virDomainObjEndAPI(&vm);
    return parent;
}

static virDomainSnapshotPtr
sfvmDomainSnapshotCurrent(virDomainPtr domain,
                          unsigned int flags)
{
    virDomainObj *vm;
    virDomainSnapshotPtr snapshot = NULL;
    virDomainMomentObj *current;

    virCheckFlags(0, NULL);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return NULL;

    current = virDomainSnapshotGetCurrent(vm->snapshots);
    if (!current) {
        virReportError(VIR_ERR_NO_DOMAIN_SNAPSHOT, "%s",
                       _("the domain does not have a current snapshot"));
        goto cleanup;
    }

    snapshot = virGetDomainSnapshot(domain, current->def->name);

 cleanup:
    virDomainObjEndAPI(&vm);
    return snapshot;
}

static char *
sfvmDomainSnapshotGetXMLDesc(virDomainSnapshotPtr snapshot,
                             unsigned int flags)
{
    virDomainObj *vm = NULL;
    char *xml = NULL;
    virDomainMomentObj *snap = NULL;
    char uuidstr[VIR_UUID_STRING_BUFLEN];
    sfvmDriver *privconn = snapshot->domain->conn->privateData;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_XML_SECURE, NULL);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return NULL;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;

    virUUIDFormat(snapshot->domain->uuid, uuidstr);

    xml = virDomainSnapshotDefFormat(uuidstr, virDomainSnapshotObjGetDef(snap),
                                     privconn->xmlopt,
                                     virDomainSnapshotFormatConvertXMLFlags(flags));

 cleanup:
    virDomainObjEndAPI(&vm);
    return xml;
}

static int
sfvmDomainSnapshotIsCurrent(virDomainSnapshotPtr snapshot,
                            unsigned int flags)
{
    virDomainObj *vm = NULL;
    int ret = -1;
    virDomainMomentObj *snap = NULL;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return -1;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;

    ret = snap == virDomainSnapshotGetCurrent(vm->snapshots);

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}


static int
sfvmDomainSnapshotHasMetadata(virDomainSnapshotPtr snapshot,
                              unsigned int flags)
{
    virDomainObj *vm = NULL;
    int ret = -1;

    virCheckFlags(0, -1);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return -1;

    if (!sfvmSnapObjFromSnapshot(vm, snapshot))
        goto cleanup;

    ret = 1;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainSnapshotAlignDisks(virDomainObj *vm,
                             virDomainSnapshotDef *def,
                             unsigned int flags)
{
    virDomainSnapshotLocation align_location = VIR_DOMAIN_SNAPSHOT_LOCATION_INTERNAL;
    size_t i;

    for (i = 0; i < def->ndisks; i++) {
        switch (def->disks[i].snapshot) {
        case VIR_DOMAIN_SNAPSHOT_LOCATION_DEFAULT:
        case VIR_DOMAIN_SNAPSHOT_LOCATION_NO:
        case VIR_DOMAIN_SNAPSHOT_LOCATION_INTERNAL:
        case VIR_DOMAIN_SNAPSHOT_LOCATION_EXTERNAL:
        case VIR_DOMAIN_SNAPSHOT_LOCATION_LAST:
            break;

        case VIR_DOMAIN_SNAPSHOT_LOCATION_MANUAL:
            virReportError(VIR_ERR_OPERATION_UNSUPPORTED, "%s",
                           _("'manual' snapshot mode is not supported by the sfvm driver"));
            return -1;
        }
    }

    if (flags & VIR_DOMAIN_SNAPSHOT_CREATE_DISK_ONLY) {
        align_location = VIR_DOMAIN_SNAPSHOT_LOCATION_EXTERNAL;
        if (virDomainObjIsActive(vm))
            def->state = VIR_DOMAIN_SNAPSHOT_DISK_SNAPSHOT;
        else
            def->state = VIR_DOMAIN_SNAPSHOT_SHUTOFF;
        def->memory = VIR_DOMAIN_SNAPSHOT_LOCATION_NO;
    } else if (def->memory == VIR_DOMAIN_SNAPSHOT_LOCATION_EXTERNAL) {
        def->state = virDomainObjGetState(vm, NULL);
        align_location = VIR_DOMAIN_SNAPSHOT_LOCATION_EXTERNAL;
    } else {
        def->state = virDomainObjGetState(vm, NULL);
        def->memory = def->state == VIR_DOMAIN_SNAPSHOT_SHUTOFF ?
                      VIR_DOMAIN_SNAPSHOT_LOCATION_NO :
                      VIR_DOMAIN_SNAPSHOT_LOCATION_INTERNAL;
    }

    return virDomainSnapshotAlignDisks(def, NULL, align_location, true);
}


static virDomainSnapshotPtr
sfvmDomainSnapshotRedefine(virDomainObj *vm,
                           virDomainPtr domain,
                           virDomainSnapshotDef *snapdeftmp,
                           virDomainMomentObj **snapout,
                           virDomainXMLOption *xmlopt,
                           unsigned int flags)
{
    virDomainMomentObj *snap = NULL;
    g_autoptr(virDomainSnapshotDef) snapdef = virObjectRef(snapdeftmp);

    if (virDomainSnapshotRedefinePrep(vm, snapdef, &snap, xmlopt, flags) < 0)
        return NULL;

    if (snap) {
        virDomainSnapshotReplaceDef(snap, &snapdef);
    } else {
        if (!(snap = virDomainSnapshotAssignDef(vm->snapshots, &snapdef)))
            return NULL;
    }

    *snapout = snap;

    return virGetDomainSnapshot(domain, snap->def->name);
}


static virDomainSnapshotPtr
sfvmDomainSnapshotCreateXML(virDomainPtr domain,
                            const char *xmlDesc,
                            unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *vm = NULL;
    virDomainMomentObj *snap = NULL;
    virDomainSnapshotPtr snapshot = NULL;
    virObjectEvent *event = NULL;
    bool update_current = true;
    bool redefine = flags & VIR_DOMAIN_SNAPSHOT_CREATE_REDEFINE;
    unsigned int parse_flags = 0;
    g_autoptr(virDomainSnapshotDef) def = NULL;

    /*
     * DISK_ONLY: Not implemented yet
     * REUSE_EXT: Not implemented yet
     *
     * NO_METADATA: Explicitly not implemented
     *
     * REDEFINE + CURRENT: Implemented
     * HALT: Implemented
     * QUIESCE: Nothing to do
     * ATOMIC: Nothing to do
     * LIVE: Nothing to do
     */
    virCheckFlags(
        VIR_DOMAIN_SNAPSHOT_CREATE_REDEFINE |
        VIR_DOMAIN_SNAPSHOT_CREATE_CURRENT |
        VIR_DOMAIN_SNAPSHOT_CREATE_HALT |
        VIR_DOMAIN_SNAPSHOT_CREATE_QUIESCE |
        VIR_DOMAIN_SNAPSHOT_CREATE_ATOMIC |
        VIR_DOMAIN_SNAPSHOT_CREATE_LIVE |
        VIR_DOMAIN_SNAPSHOT_CREATE_VALIDATE, NULL);

    if ((redefine && !(flags & VIR_DOMAIN_SNAPSHOT_CREATE_CURRENT)))
        update_current = false;
    if (redefine)
        parse_flags |= VIR_DOMAIN_SNAPSHOT_PARSE_REDEFINE;

    if (!(vm = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainListCheckpoints(vm->checkpoints, NULL, domain, NULL, 0) > 0) {
        virReportError(VIR_ERR_OPERATION_UNSUPPORTED, "%s",
                       _("cannot create snapshot while checkpoint exists"));
        goto cleanup;
    }

    if (!vm->persistent && (flags & VIR_DOMAIN_SNAPSHOT_CREATE_HALT)) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("cannot halt after transient domain snapshot"));
        goto cleanup;
    }

    if (flags & VIR_DOMAIN_SNAPSHOT_CREATE_VALIDATE)
        parse_flags |= VIR_DOMAIN_SNAPSHOT_PARSE_VALIDATE;

    if (!(def = virDomainSnapshotDefParseString(xmlDesc,
                                                privconn->xmlopt,
                                                NULL, NULL,
                                                parse_flags)))
        goto cleanup;

    if (redefine) {
        snapshot = sfvmDomainSnapshotRedefine(vm, domain, def, &snap,
                                              privconn->xmlopt, flags);
        goto cleanup;
    }

    if (!(def->parent.dom = virDomainDefCopy(vm->def,
                                             privconn->xmlopt,
                                             NULL,
                                             true)))
        goto cleanup;

    if (sfvmDomainSnapshotAlignDisks(vm, def, flags) < 0)
        goto cleanup;

    if (!(snap = virDomainSnapshotAssignDef(vm->snapshots, &def)))
        goto cleanup;

    snap->def->parent_name = g_strdup(virDomainSnapshotGetCurrentName(vm->snapshots));

    if ((flags & VIR_DOMAIN_SNAPSHOT_CREATE_HALT) &&
        virDomainObjIsActive(vm)) {
        sfvmDomainShutdownState(domain, vm,
                                VIR_DOMAIN_SHUTOFF_FROM_SNAPSHOT);
        event = virDomainEventLifecycleNewFromObj(vm, VIR_DOMAIN_EVENT_STOPPED,
                                                  VIR_DOMAIN_EVENT_STOPPED_FROM_SNAPSHOT);
    }

    snapshot = virGetDomainSnapshot(domain, snap->def->name);
 cleanup:
    if (vm) {
        if (snapshot) {
            if (update_current)
                virDomainSnapshotSetCurrent(vm->snapshots, snap);
            virDomainSnapshotLinkParent(vm->snapshots, snap);
        }
        virDomainObjEndAPI(&vm);
    }
    virObjectEventStateQueue(privconn->eventState, event);
    return snapshot;
}


typedef struct _sfvmMomentRemoveData sfvmMomentRemoveData;
struct _sfvmMomentRemoveData {
    virDomainObj *vm;
    bool current;
};

static int
sfvmDomainSnapshotDiscardAll(void *payload,
                             const char *name G_GNUC_UNUSED,
                             void *data)
{
    virDomainMomentObj *snap = payload;
    sfvmMomentRemoveData *curr = data;

    curr->current |= virDomainSnapshotObjListRemove(curr->vm->snapshots, snap);
    return 0;
}

typedef struct _sfvmMomentReparentData sfvmMomentReparentData;
struct _sfvmMomentReparentData {
    virDomainMomentObj *parent;
    virDomainObj *vm;
    int err;
};

static int
sfvmDomainMomentReparentChildren(void *payload,
                                 const char *name G_GNUC_UNUSED,
                                 void *data)
{
    virDomainMomentObj *moment = payload;
    sfvmMomentReparentData *rep = data;

    if (rep->err < 0)
        return 0;

    VIR_FREE(moment->def->parent_name);

    if (rep->parent->def)
        moment->def->parent_name = g_strdup(rep->parent->def->name);

    return 0;
}

static int
sfvmDomainSnapshotDelete(virDomainSnapshotPtr snapshot,
                         unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainMomentObj *snap = NULL;
    virDomainMomentObj *parentsnap = NULL;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_DELETE_CHILDREN |
                  VIR_DOMAIN_SNAPSHOT_DELETE_CHILDREN_ONLY, -1);

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return -1;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;

    if (flags & (VIR_DOMAIN_SNAPSHOT_DELETE_CHILDREN |
                 VIR_DOMAIN_SNAPSHOT_DELETE_CHILDREN_ONLY)) {
        sfvmMomentRemoveData rem;
        rem.vm = vm;
        rem.current = false;
        virDomainMomentForEachDescendant(snap,
                                         sfvmDomainSnapshotDiscardAll,
                                         &rem);
        if (rem.current)
            virDomainSnapshotSetCurrent(vm->snapshots, snap);
    } else if (snap->nchildren) {
        sfvmMomentReparentData rep;
        rep.parent = snap->parent;
        rep.vm = vm;
        rep.err = 0;
        virDomainMomentForEachChild(snap,
                                    sfvmDomainMomentReparentChildren,
                                    &rep);
        if (rep.err < 0)
            goto cleanup;

        virDomainMomentMoveChildren(snap, snap->parent);
    }

    if (flags & VIR_DOMAIN_SNAPSHOT_DELETE_CHILDREN_ONLY) {
        virDomainMomentDropChildren(snap);
    } else {
        virDomainMomentDropParent(snap);
        if (snap == virDomainSnapshotGetCurrent(vm->snapshots)) {
            if (snap->def->parent_name) {
                parentsnap = virDomainSnapshotFindByName(vm->snapshots,
                                                         snap->def->parent_name);
                if (!parentsnap)
                    VIR_WARN("missing parent snapshot matching name '%s'",
                             snap->def->parent_name);
            }
            virDomainSnapshotSetCurrent(vm->snapshots, parentsnap);
        }
        virDomainSnapshotObjListRemove(vm->snapshots, snap);
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainRevertToSnapshot(virDomainSnapshotPtr snapshot,
                           unsigned int flags)
{
    sfvmDriver *privconn = snapshot->domain->conn->privateData;
    virDomainObj *vm = NULL;
    virDomainMomentObj *snap = NULL;
    virObjectEvent *event = NULL;
    virObjectEvent *event2 = NULL;
    virDomainDef *config = NULL;
    virDomainSnapshotDef *snapdef;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_SNAPSHOT_REVERT_RUNNING |
                  VIR_DOMAIN_SNAPSHOT_REVERT_PAUSED |
                  VIR_DOMAIN_SNAPSHOT_REVERT_FORCE, -1);

    /* We have the following transitions, which create the following events:
     * 1. inactive -> inactive: none
     * 2. inactive -> running:  EVENT_STARTED
     * 3. inactive -> paused:   EVENT_STARTED, EVENT_SUSPENDED
     * 4. running  -> inactive: EVENT_STOPPED
     * 5. running  -> running:  EVENT_STOPPED, EVENT_STARTED
     * 6. running  -> paused:   EVENT_STOPPED, EVENT_STARTED, EVENT_SUSPENDED
     * 7. paused   -> inactive: EVENT_STOPPED
     * 8. paused   -> running:  EVENT_STOPPED, EVENT_STARTED
     * 9. paused   -> paused:   EVENT_STOPPED, EVENT_STARTED, EVENT_SUSPENDED
     * Also, several transitions occur even if we fail partway through.
     */

    if (!(vm = sfvmDomObjFromSnapshot(snapshot)))
        return -1;

    if (!(snap = sfvmSnapObjFromSnapshot(vm, snapshot)))
        goto cleanup;
    snapdef = virDomainSnapshotObjGetDef(snap);

    if (!vm->persistent &&
        snapdef->state != VIR_DOMAIN_SNAPSHOT_RUNNING &&
        snapdef->state != VIR_DOMAIN_SNAPSHOT_PAUSED &&
        (flags & (VIR_DOMAIN_SNAPSHOT_REVERT_RUNNING |
                  VIR_DOMAIN_SNAPSHOT_REVERT_PAUSED)) == 0) {
        virReportError(VIR_ERR_OPERATION_INVALID, "%s",
                       _("transient domain needs to request run or pause "
                         "to revert to inactive snapshot"));
        goto cleanup;
    }

    if (!snap->def->dom) {
        virReportError(VIR_ERR_SNAPSHOT_REVERT_RISKY,
                       _("snapshot '%s' lacks domain '%s' rollback info"),
                       snap->def->name, vm->def->name);
        goto cleanup;
    }

    virDomainSnapshotSetCurrent(vm->snapshots, NULL);

    config = virDomainDefCopy(snap->def->dom,
                              privconn->xmlopt, NULL, true);
    if (!config)
        goto cleanup;

    if (snapdef->state == VIR_DOMAIN_SNAPSHOT_RUNNING ||
        snapdef->state == VIR_DOMAIN_SNAPSHOT_PAUSED) {
        /* Transitions 2, 3, 5, 6, 8, 9 */

        if (virDomainObjIsActive(vm)) {
            /* Transitions 5, 6, 8, 9 */
            sfvmDomainShutdownState(snapshot->domain, vm,
                                    VIR_DOMAIN_SHUTOFF_FROM_SNAPSHOT);
            event = virDomainEventLifecycleNewFromObj(vm,
                                                      VIR_DOMAIN_EVENT_STOPPED,
                                                      VIR_DOMAIN_EVENT_STOPPED_FROM_SNAPSHOT);
            virObjectEventStateQueue(privconn->eventState, event);
        }

        virDomainObjAssignDef(vm, &config, false, NULL);
        if (sfvmDomainStartState(privconn, vm,
                            VIR_DOMAIN_RUNNING_FROM_SNAPSHOT) < 0)
            goto cleanup;
        event = virDomainEventLifecycleNewFromObj(vm,
                            VIR_DOMAIN_EVENT_STARTED,
                            VIR_DOMAIN_EVENT_STARTED_FROM_SNAPSHOT);

        /* Touch up domain state.  */
        if (!(flags & VIR_DOMAIN_SNAPSHOT_REVERT_RUNNING) &&
            (snapdef->state == VIR_DOMAIN_SNAPSHOT_PAUSED ||
             (flags & VIR_DOMAIN_SNAPSHOT_REVERT_PAUSED))) {
            /* Transitions 3, 6, 9 */
            virDomainObjSetState(vm, VIR_DOMAIN_PAUSED,
                                 VIR_DOMAIN_PAUSED_FROM_SNAPSHOT);
            event2 = virDomainEventLifecycleNewFromObj(vm,
                            VIR_DOMAIN_EVENT_SUSPENDED,
                            VIR_DOMAIN_EVENT_SUSPENDED_FROM_SNAPSHOT);
        }
    } else {
        /* Transitions 1, 4, 7 */
        virDomainObjAssignDef(vm, &config, false, NULL);

        if (virDomainObjIsActive(vm)) {
            /* Transitions 4, 7 */
            sfvmDomainShutdownState(snapshot->domain, vm,
                                    VIR_DOMAIN_SHUTOFF_FROM_SNAPSHOT);
            event = virDomainEventLifecycleNewFromObj(vm,
                                    VIR_DOMAIN_EVENT_STOPPED,
                                    VIR_DOMAIN_EVENT_STOPPED_FROM_SNAPSHOT);
        }

        if (flags & (VIR_DOMAIN_SNAPSHOT_REVERT_RUNNING |
                     VIR_DOMAIN_SNAPSHOT_REVERT_PAUSED)) {
            /* Flush first event, now do transition 2 or 3 */
            bool paused = (flags & VIR_DOMAIN_SNAPSHOT_REVERT_PAUSED) != 0;

            virObjectEventStateQueue(privconn->eventState, event);
            event = virDomainEventLifecycleNewFromObj(vm,
                            VIR_DOMAIN_EVENT_STARTED,
                            VIR_DOMAIN_EVENT_STARTED_FROM_SNAPSHOT);
            if (paused) {
                event2 = virDomainEventLifecycleNewFromObj(vm,
                                VIR_DOMAIN_EVENT_SUSPENDED,
                                VIR_DOMAIN_EVENT_SUSPENDED_FROM_SNAPSHOT);
            }
        }
    }

    virDomainSnapshotSetCurrent(vm->snapshots, snap);
    ret = 0;
 cleanup:
    if (event) {
        virObjectEventStateQueue(privconn->eventState, event);
        virObjectEventStateQueue(privconn->eventState, event2);
    } else {
        virObjectUnref(event2);
    }
    virDomainObjEndAPI(&vm);

    return ret;
}

/*
 * Checkpoint APIs
 */

static int
sfvmDomainCheckpointDiscardAll(void *payload,
                               const char *name G_GNUC_UNUSED,
                               void *data)
{
    virDomainMomentObj *chk = payload;
    sfvmMomentRemoveData *curr = data;

    curr->current |= virDomainCheckpointObjListRemove(curr->vm->checkpoints,
                                                      chk);
    return 0;
}

static virDomainObj *
sfvmDomObjFromCheckpoint(virDomainCheckpointPtr checkpoint)
{
    return sfvmDomObjFromDomain(checkpoint->domain);
}

static virDomainMomentObj *
sfvmCheckpointObjFromName(virDomainObj *vm,
                          const char *name)
{
    virDomainMomentObj *chk = NULL;

    chk = virDomainCheckpointFindByName(vm->checkpoints, name);
    if (!chk)
        virReportError(VIR_ERR_NO_DOMAIN_CHECKPOINT,
                       _("no domain checkpoint with matching name '%s'"),
                       name);

    return chk;
}

static virDomainMomentObj *
sfvmCheckpointObjFromCheckpoint(virDomainObj *vm,
                           virDomainCheckpointPtr checkpoint)
{
    return sfvmCheckpointObjFromName(vm, checkpoint->name);
}

static virDomainCheckpointPtr
sfvmDomainCheckpointCreateXML(virDomainPtr domain,
                              const char *xmlDesc,
                              unsigned int flags)
{
    sfvmDriver *privconn = domain->conn->privateData;
    virDomainObj *vm = NULL;
    virDomainMomentObj *chk = NULL;
    virDomainCheckpointPtr checkpoint = NULL;
    virDomainMomentObj *current = NULL;
    bool update_current = true;
    bool redefine = flags & VIR_DOMAIN_CHECKPOINT_CREATE_REDEFINE;
    unsigned int parse_flags = 0;
    g_autoptr(virDomainCheckpointDef) def = NULL;

    virCheckFlags(VIR_DOMAIN_CHECKPOINT_CREATE_REDEFINE |
                  VIR_DOMAIN_CHECKPOINT_CREATE_QUIESCE, NULL);

    if (redefine) {
        parse_flags |= VIR_DOMAIN_CHECKPOINT_PARSE_REDEFINE;
        update_current = false;
    }

    if (!(vm = sfvmDomObjFromDomain(domain)))
        goto cleanup;

    if (virDomainSnapshotObjListNum(vm->snapshots, NULL, 0) > 0) {
        virReportError(VIR_ERR_OPERATION_UNSUPPORTED, "%s",
                       _("cannot create checkpoint while snapshot exists"));
        goto cleanup;
    }

    if (!virDomainObjIsActive(vm)) {
        virReportError(VIR_ERR_OPERATION_UNSUPPORTED, "%s",
                       _("cannot create checkpoint for inactive domain"));
        goto cleanup;
    }

    if (!(def = virDomainCheckpointDefParseString(xmlDesc,
                                                  privconn->xmlopt, NULL,
                                                  parse_flags)))
        goto cleanup;

    if (redefine) {
        if (virDomainCheckpointRedefinePrep(vm, def, &update_current) < 0)
            goto cleanup;

        if (!(chk = virDomainCheckpointRedefineCommit(vm, &def)))
            goto cleanup;
    } else {
        if (!(def->parent.dom = virDomainDefCopy(vm->def,
                                                 privconn->xmlopt,
                                                 NULL,
                                                 true)))
            goto cleanup;

        if (virDomainCheckpointAlignDisks(def) < 0)
            goto cleanup;

        if (!(chk = virDomainCheckpointAssignDef(vm->checkpoints, def)))
            goto cleanup;

        def = NULL;
    }

    current = virDomainCheckpointGetCurrent(vm->checkpoints);
    if (current) {
        if (!redefine)
            chk->def->parent_name = g_strdup(current->def->name);
        if (update_current)
            virDomainCheckpointSetCurrent(vm->checkpoints, NULL);
    }

    /* actually do the checkpoint - except the sfvm driver has nothing
     * to actually do here */

    /* If we fail after this point, there's not a whole lot we can do;
     * we've successfully created the checkpoint, so we have to go
     * forward the best we can.
     */
    checkpoint = virGetDomainCheckpoint(domain, chk->def->name);

 cleanup:
    if (checkpoint) {
        if (update_current)
            virDomainCheckpointSetCurrent(vm->checkpoints, chk);
        virDomainCheckpointLinkParent(vm->checkpoints, chk);
    } else if (chk) {
        virDomainCheckpointObjListRemove(vm->checkpoints, chk);
    }

    virDomainObjEndAPI(&vm);
    return checkpoint;
}


static int
sfvmDomainListAllCheckpoints(virDomainPtr domain,
                             virDomainCheckpointPtr **chks,
                             unsigned int flags)
{
    virDomainObj *vm = NULL;
    int n = -1;

    virCheckFlags(VIR_DOMAIN_CHECKPOINT_LIST_ROOTS |
                  VIR_DOMAIN_CHECKPOINT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_CHECKPOINT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return -1;

    n = virDomainListCheckpoints(vm->checkpoints, NULL, domain, chks, flags);

    virDomainObjEndAPI(&vm);
    return n;
}


static int
sfvmDomainCheckpointListAllChildren(virDomainCheckpointPtr checkpoint,
                                    virDomainCheckpointPtr **chks,
                                    unsigned int flags)
{
    virDomainObj *vm = NULL;
    virDomainMomentObj *chk = NULL;
    int n = -1;

    virCheckFlags(VIR_DOMAIN_CHECKPOINT_LIST_DESCENDANTS |
                  VIR_DOMAIN_CHECKPOINT_LIST_TOPOLOGICAL |
                  VIR_DOMAIN_CHECKPOINT_FILTERS_ALL, -1);

    if (!(vm = sfvmDomObjFromCheckpoint(checkpoint)))
        return -1;

    if (!(chk = sfvmCheckpointObjFromCheckpoint(vm, checkpoint)))
        goto cleanup;

    n = virDomainListCheckpoints(vm->checkpoints, chk, checkpoint->domain,
                                 chks, flags);

 cleanup:
    virDomainObjEndAPI(&vm);
    return n;
}


static virDomainCheckpointPtr
sfvmDomainCheckpointLookupByName(virDomainPtr domain,
                                 const char *name,
                                 unsigned int flags)
{
    virDomainObj *vm;
    virDomainMomentObj *chk = NULL;
    virDomainCheckpointPtr checkpoint = NULL;

    virCheckFlags(0, NULL);

    if (!(vm = sfvmDomObjFromDomain(domain)))
        return NULL;

    if (!(chk = sfvmCheckpointObjFromName(vm, name)))
        goto cleanup;

    checkpoint = virGetDomainCheckpoint(domain, chk->def->name);

 cleanup:
    virDomainObjEndAPI(&vm);
    return checkpoint;
}


static virDomainCheckpointPtr
sfvmDomainCheckpointGetParent(virDomainCheckpointPtr checkpoint,
                              unsigned int flags)
{
    virDomainObj *vm;
    virDomainMomentObj *chk = NULL;
    virDomainCheckpointPtr parent = NULL;

    virCheckFlags(0, NULL);

    if (!(vm = sfvmDomObjFromCheckpoint(checkpoint)))
        return NULL;

    if (!(chk = sfvmCheckpointObjFromCheckpoint(vm, checkpoint)))
        goto cleanup;

    if (!chk->def->parent_name) {
        virReportError(VIR_ERR_NO_DOMAIN_CHECKPOINT,
                       _("checkpoint '%s' does not have a parent"),
                       chk->def->name);
        goto cleanup;
    }

    parent = virGetDomainCheckpoint(checkpoint->domain, chk->def->parent_name);

 cleanup:
    virDomainObjEndAPI(&vm);
    return parent;
}


static char *
sfvmDomainCheckpointGetXMLDesc(virDomainCheckpointPtr checkpoint,
                               unsigned int flags)
{
    sfvmDriver *privconn = checkpoint->domain->conn->privateData;
    virDomainObj *vm = NULL;
    char *xml = NULL;
    virDomainMomentObj *chk = NULL;
    size_t i;
    virDomainCheckpointDef *chkdef;
    unsigned int format_flags;

    virCheckFlags(VIR_DOMAIN_CHECKPOINT_XML_SECURE |
                  VIR_DOMAIN_CHECKPOINT_XML_NO_DOMAIN |
                  VIR_DOMAIN_CHECKPOINT_XML_SIZE, NULL);

    if (!(vm = sfvmDomObjFromCheckpoint(checkpoint)))
        return NULL;

    if (!(chk = sfvmCheckpointObjFromCheckpoint(vm, checkpoint)))
        goto cleanup;
    chkdef = virDomainCheckpointObjGetDef(chk);

    if (flags & VIR_DOMAIN_CHECKPOINT_XML_SIZE) {
        if (virDomainObjCheckActive(vm) < 0)
            goto cleanup;

        for (i = 0; i < chkdef->ndisks; i++) {
            virDomainCheckpointDiskDef *disk = &chkdef->disks[i];

            if (disk->type != VIR_DOMAIN_CHECKPOINT_TYPE_BITMAP)
                continue;
            disk->size = 1024; /* Any number will do... */
        }
    }

    format_flags = virDomainCheckpointFormatConvertXMLFlags(flags);
    xml = virDomainCheckpointDefFormat(chkdef,
                                       privconn->xmlopt, format_flags);

 cleanup:
    virDomainObjEndAPI(&vm);
    return xml;
}


static int
sfvmDomainCheckpointDelete(virDomainCheckpointPtr checkpoint,
                           unsigned int flags)
{
    virDomainObj *vm = NULL;
    int ret = -1;
    virDomainMomentObj *chk = NULL;
    virDomainMomentObj *parentchk = NULL;

    virCheckFlags(VIR_DOMAIN_CHECKPOINT_DELETE_CHILDREN |
                  VIR_DOMAIN_CHECKPOINT_DELETE_METADATA_ONLY |
                  VIR_DOMAIN_CHECKPOINT_DELETE_CHILDREN_ONLY, -1);

    if (!(vm = sfvmDomObjFromCheckpoint(checkpoint)))
        return -1;

    if (!(chk = sfvmCheckpointObjFromCheckpoint(vm, checkpoint)))
        goto cleanup;

    if (flags & (VIR_DOMAIN_CHECKPOINT_DELETE_CHILDREN |
                 VIR_DOMAIN_CHECKPOINT_DELETE_CHILDREN_ONLY)) {
        sfvmMomentRemoveData rem;

        rem.vm = vm;
        rem.current = false;
        virDomainMomentForEachDescendant(chk, sfvmDomainCheckpointDiscardAll,
                                         &rem);
        if (rem.current)
            virDomainCheckpointSetCurrent(vm->checkpoints, chk);
    } else if (chk->nchildren) {
        sfvmMomentReparentData rep;

        rep.parent = chk->parent;
        rep.vm = vm;
        rep.err = 0;
        virDomainMomentForEachChild(chk, sfvmDomainMomentReparentChildren,
                                    &rep);
        if (rep.err < 0)
            goto cleanup;
        virDomainMomentMoveChildren(chk, chk->parent);
    }

    if (flags & VIR_DOMAIN_CHECKPOINT_DELETE_CHILDREN_ONLY) {
        virDomainMomentDropChildren(chk);
    } else {
        virDomainMomentDropParent(chk);
        if (chk == virDomainCheckpointGetCurrent(vm->checkpoints)) {
            if (chk->def->parent_name) {
                parentchk = virDomainCheckpointFindByName(vm->checkpoints,
                                                          chk->def->parent_name);
                if (!parentchk)
                    VIR_WARN("missing parent checkpoint matching name '%s'",
                             chk->def->parent_name);
            }
            virDomainCheckpointSetCurrent(vm->checkpoints, parentchk);
        }
        virDomainCheckpointObjListRemove(vm->checkpoints, chk);
    }

    ret = 0;
 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainGetMessages(virDomainPtr dom,
                      char ***msgs,
                      unsigned int flags)
{
    virDomainObj *vm = NULL;
    int rv = -1;

    virCheckFlags(VIR_DOMAIN_MESSAGE_DEPRECATION |
                  VIR_DOMAIN_MESSAGE_TAINTING, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        return -1;

    rv = virDomainObjGetMessages(vm, msgs, flags);

    virDomainObjEndAPI(&vm);
    return rv;
}

static int
sfvmDomainGetIOThreadInfo(virDomainPtr dom,
                          virDomainIOThreadInfoPtr **info,
                          unsigned int flags)
{
    virDomainObj *vm;
    virDomainDef *targetDef = NULL;
    unsigned int bitmap_size = 0;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(targetDef = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    bitmap_size = virDomainDefGetVcpus(targetDef);

    ret = virDomainDriverGetIOThreadsConfig(targetDef, info, bitmap_size);

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

typedef enum {
    VIR_DOMAIN_IOTHREAD_ACTION_ADD,
    VIR_DOMAIN_IOTHREAD_ACTION_DEL,
    VIR_DOMAIN_IOTHREAD_ACTION_MOD,
} virDomainIOThreadAction;

static int
sfvmDomainChgIOThread(virDomainObj *vm,
                      unsigned int iothread_id,
                      virDomainIOThreadAction action,
                      unsigned int flags)
{
    virDomainDef *def;
    int ret = -1;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        return ret;

    if (def) {
        switch (action) {
        case VIR_DOMAIN_IOTHREAD_ACTION_ADD:
            if (virDomainDriverAddIOThreadCheck(def, iothread_id) < 0)
                return ret;

            if (!virDomainIOThreadIDAdd(def, iothread_id))
                return ret;

            break;

        case VIR_DOMAIN_IOTHREAD_ACTION_DEL:
            if (virDomainDriverDelIOThreadCheck(def, iothread_id) < 0)
                return ret;

            virDomainIOThreadIDDel(def, iothread_id);

            break;

        case VIR_DOMAIN_IOTHREAD_ACTION_MOD:
            if (!(virDomainIOThreadIDFind(def, iothread_id))) {
                virReportError(VIR_ERR_INVALID_ARG,
                               _("cannot find IOThread '%u' in iothreadids"),
                               iothread_id);
                return ret;
            }

            break;
        }
    }

    ret = 0;

    return ret;
}

static int
sfvmDomainAddIOThread(virDomainPtr dom,
                      unsigned int iothread_id,
                      unsigned int flags)
{
    virDomainObj *vm = NULL;
    sfvmDomainObjPrivate *priv;
    sfvmIOThreadInfo iothread;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (iothread_id == 0) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("invalid value of 0 for iothread_id"));
        return -1;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (sfvmDomainChgIOThread(vm, iothread_id,
                              VIR_DOMAIN_IOTHREAD_ACTION_ADD, flags) < 0)
        goto cleanup;

    priv = vm->privateData;

    iothread.iothread_id = iothread_id;
    iothread.poll_max_ns = 32768;
    iothread.poll_grow = 0;
    iothread.poll_shrink = 0;

    g_array_append_val(priv->iothreads, iothread);

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainDelIOThread(virDomainPtr dom,
                      unsigned int iothread_id,
                      unsigned int flags)
{
    virDomainObj *vm = NULL;
    sfvmDomainObjPrivate *priv;
    size_t i;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (iothread_id == 0) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("invalid value of 0 for iothread_id"));
        return -1;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (sfvmDomainChgIOThread(vm, iothread_id,
                              VIR_DOMAIN_IOTHREAD_ACTION_DEL, flags) < 0)
        goto cleanup;

    priv = vm->privateData;

    for (i = 0; i < priv->iothreads->len; i++) {
        sfvmIOThreadInfo iothread = g_array_index(priv->iothreads,
                                                  sfvmIOThreadInfo, i);
        if (iothread.iothread_id == iothread_id) {
            g_array_remove_index(priv->iothreads, i);
            break;
        }
    }

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainPinIOThread(virDomainPtr dom,
                      unsigned int iothread_id,
                      unsigned char *cpumap,
                      int maplen,
                      unsigned int flags)
{
    int ret = -1;
    virDomainObj *vm;
    virDomainDef *def;
    virDomainIOThreadIDDef *iothrid;
    g_autoptr(virBitmap) cpumask = NULL;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE |
                  VIR_DOMAIN_AFFECT_CONFIG, -1);

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (!(def = virDomainObjGetOneDef(vm, flags)))
        goto cleanup;

    if (!(cpumask = virBitmapNewData(cpumap, maplen)))
        goto cleanup;

    if (virBitmapIsAllClear(cpumask)) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("Empty iothread cpumap list for pinning"));
        goto cleanup;
    }

    if (!(iothrid = virDomainIOThreadIDFind(def, iothread_id))) {
        virReportError(VIR_ERR_INVALID_ARG,
                       _("iothreadid %d not found"), iothread_id);
        goto cleanup;
    }

    virBitmapFree(iothrid->cpumask);
    iothrid->cpumask = g_steal_pointer(&cpumask);
    iothrid->autofill = false;

    ret = 0;

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainIOThreadParseParams(virTypedParameterPtr params,
                              int nparams,
                              sfvmIOThreadInfo *iothread)
{
    if (virTypedParamsValidate(params, nparams,
                               VIR_DOMAIN_IOTHREAD_POLL_MAX_NS,
                               VIR_TYPED_PARAM_ULLONG,
                               VIR_DOMAIN_IOTHREAD_POLL_GROW,
                               VIR_TYPED_PARAM_UINT,
                               VIR_DOMAIN_IOTHREAD_POLL_SHRINK,
                               VIR_TYPED_PARAM_UINT,
                               NULL) < 0)
        return -1;

    if (virTypedParamsGetULLong(params, nparams,
                                VIR_DOMAIN_IOTHREAD_POLL_MAX_NS,
                                &iothread->poll_max_ns) < 0)
        return -1;

    if (virTypedParamsGetUInt(params, nparams,
                              VIR_DOMAIN_IOTHREAD_POLL_GROW,
                              &iothread->poll_grow) < 0)
        return -1;

    if (virTypedParamsGetUInt(params, nparams,
                              VIR_DOMAIN_IOTHREAD_POLL_SHRINK,
                              &iothread->poll_shrink) < 0)
        return -1;

    return 0;
}

static int
sfvmDomainSetIOThreadParams(virDomainPtr dom,
                            unsigned int iothread_id,
                            virTypedParameterPtr params,
                            int nparams,
                            unsigned int flags)
{
    virDomainObj *vm = NULL;
    sfvmDomainObjPrivate *priv;
    size_t i;
    int ret = -1;

    virCheckFlags(VIR_DOMAIN_AFFECT_LIVE, -1);

    if (iothread_id == 0) {
        virReportError(VIR_ERR_INVALID_ARG, "%s",
                       _("invalid value of 0 for iothread_id"));
        goto cleanup;
    }

    if (!(vm = sfvmDomObjFromDomain(dom)))
        goto cleanup;

    if (sfvmDomainChgIOThread(vm, iothread_id,
                              VIR_DOMAIN_IOTHREAD_ACTION_MOD, flags) < 0)
        goto cleanup;

    priv = vm->privateData;

    for (i = 0; i < priv->iothreads->len; i++) {
        sfvmIOThreadInfo *iothread = &g_array_index(priv->iothreads,
                                                    sfvmIOThreadInfo, i);
        if (iothread->iothread_id == iothread_id) {
            if (sfvmDomainIOThreadParseParams(params, nparams, iothread) < 0)
                goto cleanup;
            ret = 0;
            break;
        }
    }

 cleanup:
    virDomainObjEndAPI(&vm);
    return ret;
}

static int
sfvmDomainGetStatsState(virDomainObj *dom,
                        virTypedParamList *params)
{
    if (virTypedParamListAddInt(params, dom->state.state, "state.state") < 0)
        return -1;

    if (virTypedParamListAddInt(params, dom->state.reason, "state.reason") < 0)
        return -1;

    return 0;
}

static int
sfvmDomainGetStatsIOThread(virDomainObj *dom,
                           virTypedParamList *params)
{
    sfvmDomainObjPrivate *priv = dom->privateData;
    size_t i;
    int niothreads = 0;

    if (!virDomainObjIsActive(dom))
        return 0;

    niothreads = priv->iothreads->len;

    if (niothreads == 0) {
        return 0;
    }

    if (virTypedParamListAddUInt(params, niothreads, "iothread.count") < 0)
        return -1;

    for (i = 0; i < niothreads; i++) {
        sfvmIOThreadInfo iothread = g_array_index(priv->iothreads,
                                                  sfvmIOThreadInfo, i);
        if (virTypedParamListAddULLong(params, iothread.poll_max_ns,
                                       "iothread.%u.poll-max-ns",
                                       iothread.iothread_id) < 0)
            return -1;
        if (virTypedParamListAddUInt(params, iothread.poll_grow,
                                     "iothread.%u.poll-grow",
                                     iothread.iothread_id) < 0)
            return -1;
        if (virTypedParamListAddUInt(params, iothread.poll_shrink,
                                     "iothread.%u.poll-shrink",
                                     iothread.iothread_id) < 0)
            return -1;
    }

    return 0;
}

typedef int
(*sfvmDomainGetStatsFunc)(virDomainObj *dom,
                          virTypedParamList *list);

struct sfvmDomainGetStatsWorker {
    sfvmDomainGetStatsFunc func;
    unsigned int stats;
};

static struct sfvmDomainGetStatsWorker sfvmDomainGetStatsWorkers[] = {
    { sfvmDomainGetStatsState, VIR_DOMAIN_STATS_STATE },
    { sfvmDomainGetStatsIOThread, VIR_DOMAIN_STATS_IOTHREAD },
    { NULL, 0 }
};

static int
sfvmDomainGetStats(virConnectPtr conn,
                   virDomainObj *dom,
                   unsigned int stats,
                   virDomainStatsRecordPtr *record)
{
    g_autofree virDomainStatsRecordPtr tmp = NULL;
    g_autoptr(virTypedParamList) params = NULL;
    size_t i;

    params = g_new0(virTypedParamList, 1);

    for (i = 0; sfvmDomainGetStatsWorkers[i].func; i++) {
        if (stats & sfvmDomainGetStatsWorkers[i].stats) {
            if (sfvmDomainGetStatsWorkers[i].func(dom, params) < 0)
                return -1;
        }
    }

    tmp = g_new0(virDomainStatsRecord, 1);

    if (!(tmp->dom = virGetDomain(conn, dom->def->name,
                                  dom->def->uuid, dom->def->id)))
        return -1;

    tmp->nparams = virTypedParamListStealParams(params, &tmp->params);
    *record = g_steal_pointer(&tmp);
    return 0;
}

static int
sfvmConnectGetAllDomainStats(virConnectPtr conn,
                             virDomainPtr *doms,
                             unsigned int ndoms,
                             unsigned int stats,
                             virDomainStatsRecordPtr **retStats,
                             unsigned int flags)
{
    sfvmDriver *driver = conn->privateData;
    unsigned int lflags = flags & (VIR_CONNECT_LIST_DOMAINS_FILTERS_ACTIVE |
                                   VIR_CONNECT_LIST_DOMAINS_FILTERS_PERSISTENT |
                                   VIR_CONNECT_LIST_DOMAINS_FILTERS_STATE);

    unsigned int supported = VIR_DOMAIN_STATS_STATE |
                             VIR_DOMAIN_STATS_IOTHREAD;
    virDomainObj **vms = NULL;
    size_t nvms;
    virDomainStatsRecordPtr *tmpstats = NULL;
    int nstats = 0;
    int ret = -1;
    size_t i;

    virCheckFlags(VIR_CONNECT_LIST_DOMAINS_FILTERS_ACTIVE |
                  VIR_CONNECT_LIST_DOMAINS_FILTERS_PERSISTENT |
                  VIR_CONNECT_LIST_DOMAINS_FILTERS_STATE |
                  VIR_CONNECT_GET_ALL_DOMAINS_STATS_NOWAIT |
                  VIR_CONNECT_GET_ALL_DOMAINS_STATS_BACKING |
                  VIR_CONNECT_GET_ALL_DOMAINS_STATS_ENFORCE_STATS, -1);

    if (!stats) {
        stats = supported;
    } else if ((flags & VIR_CONNECT_GET_ALL_DOMAINS_STATS_ENFORCE_STATS) &&
               (stats & ~supported)) {
        virReportError(VIR_ERR_ARGUMENT_UNSUPPORTED,
                       _("Stats types bits 0x%x are not supported by this daemon"),
                       stats & ~supported);
        return -1;
    }

    if (ndoms) {
        if (virDomainObjListConvert(driver->domains, conn, doms, ndoms, &vms,
                                    &nvms, NULL, lflags, true) < 0)
            return -1;
    } else {
        virDomainObjListCollect(driver->domains, conn, &vms, &nvms, NULL, lflags);
    }

    tmpstats = g_new0(virDomainStatsRecordPtr, nvms + 1);

    for (i = 0; i < nvms; i++) {
        virDomainStatsRecordPtr tmp = NULL;
        virDomainObj *vm = vms[i];

        virObjectLock(vm);

        if ((sfvmDomainGetStats(conn, vm, stats, &tmp)) < 0) {
            virObjectUnlock(vm);
            goto cleanup;
        }

        virObjectUnlock(vm);

        if (!tmp)
            goto cleanup;

        tmpstats[nstats++] = tmp;
    }

    *retStats = g_steal_pointer(&tmpstats);
    ret = nstats;

 cleanup:
    virDomainStatsRecordListFree(tmpstats);
    virObjectListFreeCount(vms, nvms);

    return ret;
}

/*
 * Test driver
 */
static virHypervisorDriver sfvmHypervisorDriver = {
    .name = "Sfvm",
    .connectOpen = sfvmConnectOpen, /* 0.1.1 */
    .connectClose = sfvmConnectClose, /* 0.1.1 */
    .connectGetVersion = sfvmConnectGetVersion, /* 0.1.1 */
    .connectGetHostname = sfvmConnectGetHostname, /* 0.6.3 */
    .connectGetMaxVcpus = sfvmConnectGetMaxVcpus, /* 0.3.2 */
    .nodeGetInfo = sfvmNodeGetInfo, /* 0.1.1 */
    .nodeGetCPUStats = sfvmNodeGetCPUStats, /* 2.3.0 */
    .nodeGetFreeMemory = sfvmNodeGetFreeMemory, /* 2.3.0 */
    .nodeGetFreePages = sfvmNodeGetFreePages, /* 2.3.0 */
    .connectGetAllDomainStats = sfvmConnectGetAllDomainStats, /* 7.8.0 */
    .connectGetCapabilities = sfvmConnectGetCapabilities, /* 0.2.1 */
    .connectGetSysinfo = sfvmConnectGetSysinfo, /* 2.3.0 */
    .connectGetType = sfvmConnectGetType, /* 2.3.0 */
    .connectSupportsFeature = sfvmConnectSupportsFeature, /* 5.6.0 */
    .connectListDomains = sfvmConnectListDomains, /* 0.1.1 */
    .connectNumOfDomains = sfvmConnectNumOfDomains, /* 0.1.1 */
    .connectListAllDomains = sfvmConnectListAllDomains, /* 0.9.13 */
    .domainCreateXML = sfvmDomainCreateXML, /* 0.1.4 */
    .domainCreateXMLWithFiles = sfvmDomainCreateXMLWithFiles, /* 5.7.0 */
    .domainLookupByID = sfvmDomainLookupByID, /* 0.1.1 */
    .domainLookupByUUID = sfvmDomainLookupByUUID, /* 0.1.1 */
    .domainLookupByName = sfvmDomainLookupByName, /* 0.1.1 */
    .domainSuspend = sfvmDomainSuspend, /* 0.1.1 */
    .domainResume = sfvmDomainResume, /* 0.1.1 */
    .domainShutdown = sfvmDomainShutdown, /* 0.1.1 */
    .domainShutdownFlags = sfvmDomainShutdownFlags, /* 0.9.10 */
    .domainReboot = sfvmDomainReboot, /* 0.1.1 */
    .domainReset = sfvmDomainReset, /* 5.7.0 */
    .domainDestroy = sfvmDomainDestroy, /* 0.1.1 */
    .domainDestroyFlags = sfvmDomainDestroyFlags, /* 4.2.0 */
    .domainGetOSType = sfvmDomainGetOSType, /* 0.1.9 */
    .domainGetLaunchSecurityInfo = sfvmDomainGetLaunchSecurityInfo, /* 5.5.0 */
    .domainGetMaxMemory = sfvmDomainGetMaxMemory, /* 0.1.4 */
    .domainSetMaxMemory = sfvmDomainSetMaxMemory, /* 0.1.1 */
    .domainSetMemory = sfvmDomainSetMemory, /* 0.1.4 */
    .domainSetMemoryStatsPeriod = sfvmDomainSetMemoryStatsPeriod, /* 5.6.0 */
    .domainSetMemoryFlags = sfvmDomainSetMemoryFlags, /* 5.6.0 */
    .domainGetHostname = sfvmDomainGetHostname, /* 5.5.0 */
    .domainGetInfo = sfvmDomainGetInfo, /* 0.1.1 */
    .domainGetState = sfvmDomainGetState, /* 0.9.2 */
    .domainGetControlInfo = sfvmDomainGetControlInfo, /* 7.6.0 */
    .domainGetTime = sfvmDomainGetTime, /* 5.4.0 */
    .domainSetTime = sfvmDomainSetTime, /* 5.7.0 */
    .domainSave = sfvmDomainSave, /* 0.3.2 */
    .domainSaveFlags = sfvmDomainSaveFlags, /* 0.9.4 */
    .domainRestore = sfvmDomainRestore, /* 0.3.2 */
    .domainRestoreFlags = sfvmDomainRestoreFlags, /* 0.9.4 */
    .domainSaveImageDefineXML = sfvmDomainSaveImageDefineXML, /* 5.5.0 */
    .domainSaveImageGetXMLDesc = sfvmDomainSaveImageGetXMLDesc, /* 5.5.0 */
    .domainCoreDump = sfvmDomainCoreDump, /* 0.3.2 */
    .domainCoreDumpWithFormat = sfvmDomainCoreDumpWithFormat, /* 1.2.3 */
    .domainSetUserPassword = sfvmDomainSetUserPassword, /* 5.6.0 */
    .domainPinEmulator = sfvmDomainPinEmulator, /* 5.6.0 */
    .domainGetEmulatorPinInfo = sfvmDomainGetEmulatorPinInfo, /* 5.6.0 */
    .domainSetVcpus = sfvmDomainSetVcpus, /* 0.1.4 */
    .domainSetVcpusFlags = sfvmDomainSetVcpusFlags, /* 0.8.5 */
    .domainGetVcpusFlags = sfvmDomainGetVcpusFlags, /* 0.8.5 */
    .domainPinVcpu = sfvmDomainPinVcpu, /* 0.7.3 */
    .domainPinVcpuFlags = sfvmDomainPinVcpuFlags, /* 5.6.0 */
    .domainGetVcpus = sfvmDomainGetVcpus, /* 0.7.3 */
    .domainGetVcpuPinInfo = sfvmDomainGetVcpuPinInfo, /* 1.2.18 */
    .domainGetMaxVcpus = sfvmDomainGetMaxVcpus, /* 0.7.3 */
    .domainGetIOThreadInfo = sfvmDomainGetIOThreadInfo, /* 7.8.0 */
    .domainAddIOThread = sfvmDomainAddIOThread, /* 7.8.0 */
    .domainDelIOThread = sfvmDomainDelIOThread, /* 7.8.0 */
    .domainPinIOThread = sfvmDomainPinIOThread, /* 7.8.0 */
    .domainSetIOThreadParams = sfvmDomainSetIOThreadParams, /* 7.8.0 */
    .domainGetSecurityLabel = sfvmDomainGetSecurityLabel, /* 7.5.0 */
    .nodeGetSecurityModel = sfvmNodeGetSecurityModel, /* 7.5.0 */
    .domainGetXMLDesc = sfvmDomainGetXMLDesc, /* 0.1.4 */
    .domainSetMemoryParameters = sfvmDomainSetMemoryParameters, /* 5.6.0 */
    .domainGetMemoryParameters = sfvmDomainGetMemoryParameters, /* 5.6.0 */
    .domainSetNumaParameters = sfvmDomainSetNumaParameters, /* 5.6.0 */
    .domainGetNumaParameters = sfvmDomainGetNumaParameters, /* 5.6.0 */
    .domainSetInterfaceParameters = sfvmDomainSetInterfaceParameters, /* 5.6.0 */
    .domainGetInterfaceParameters = sfvmDomainGetInterfaceParameters, /* 5.6.0 */
    .domainSetBlockIoTune = sfvmDomainSetBlockIoTune, /* 5.7.0 */
    .domainGetBlockIoTune = sfvmDomainGetBlockIoTune, /* 5.7.0 */
    .domainSetBlkioParameters = sfvmDomainSetBlkioParameters, /* 7.7.0 */
    .domainGetBlkioParameters = sfvmDomainGetBlkioParameters, /* 7.7.0 */
    .connectListDefinedDomains = sfvmConnectListDefinedDomains, /* 0.1.11 */
    .connectNumOfDefinedDomains = sfvmConnectNumOfDefinedDomains, /* 0.1.11 */
    .domainCreate = sfvmDomainCreate, /* 0.1.11 */
    .domainCreateWithFlags = sfvmDomainCreateWithFlags, /* 0.8.2 */
    .domainCreateWithFiles = sfvmDomainCreateWithFiles, /* 5.7.0 */
    .domainDefineXML = sfvmDomainDefineXML, /* 0.1.11 */
    .domainDefineXMLFlags = sfvmDomainDefineXMLFlags, /* 1.2.12 */
    .domainUndefine = sfvmDomainUndefine, /* 0.1.11 */
    .domainUndefineFlags = sfvmDomainUndefineFlags, /* 0.9.4 */
    .domainFSFreeze = sfvmDomainFSFreeze, /* 5.7.0 */
    .domainFSThaw = sfvmDomainFSThaw, /* 5.7.0 */
    .domainFSTrim = sfvmDomainFSTrim, /* 5.7.0 */
    .domainGetAutostart = sfvmDomainGetAutostart, /* 0.3.2 */
    .domainSetAutostart = sfvmDomainSetAutostart, /* 0.3.2 */
    .domainGetDiskErrors = sfvmDomainGetDiskErrors, /* 5.4.0 */
    .domainGetFSInfo = sfvmDomainGetFSInfo, /* 5.6.0 */
    .domainSetPerfEvents = sfvmDomainSetPerfEvents, /* 5.6.0 */
    .domainGetPerfEvents = sfvmDomainGetPerfEvents, /* 5.6.0 */
    .domainGetSchedulerType = sfvmDomainGetSchedulerType, /* 0.3.2 */
    .domainGetSchedulerParameters = sfvmDomainGetSchedulerParameters, /* 0.3.2 */
    .domainGetSchedulerParametersFlags = sfvmDomainGetSchedulerParametersFlags, /* 0.9.2 */
    .domainSetSchedulerParameters = sfvmDomainSetSchedulerParameters, /* 0.3.2 */
    .domainSetSchedulerParametersFlags = sfvmDomainSetSchedulerParametersFlags, /* 0.9.2 */
    .domainBlockStats = sfvmDomainBlockStats, /* 0.7.0 */
    .domainInterfaceAddresses = sfvmDomainInterfaceAddresses, /* 5.4.0 */
    .domainInterfaceStats = sfvmDomainInterfaceStats, /* 0.7.0 */
    .nodeGetCellsFreeMemory = sfvmNodeGetCellsFreeMemory, /* 0.4.2 */
    .connectDomainEventRegister = sfvmConnectDomainEventRegister, /* 0.6.0 */
    .connectDomainEventDeregister = sfvmConnectDomainEventDeregister, /* 0.6.0 */
    .connectIsEncrypted = sfvmConnectIsEncrypted, /* 0.7.3 */
    .connectIsSecure = sfvmConnectIsSecure, /* 0.7.3 */
    .domainIsActive = sfvmDomainIsActive, /* 0.7.3 */
    .domainIsPersistent = sfvmDomainIsPersistent, /* 0.7.3 */
    .domainIsUpdated = sfvmDomainIsUpdated, /* 0.8.6 */
    .connectDomainEventRegisterAny = sfvmConnectDomainEventRegisterAny, /* 0.8.0 */
    .connectDomainEventDeregisterAny = sfvmConnectDomainEventDeregisterAny, /* 0.8.0 */
    .connectIsAlive = sfvmConnectIsAlive, /* 0.9.8 */
    .nodeGetCPUMap = sfvmNodeGetCPUMap, /* 1.0.0 */
    .domainRename = sfvmDomainRename, /* 4.1.0 */
    .domainScreenshot = sfvmDomainScreenshot, /* 1.0.5 */
    .domainInjectNMI = sfvmDomainInjectNMI, /* 5.6.0 */
    .domainSendKey = sfvmDomainSendKey, /* 5.5.0 */
    .domainGetMetadata = sfvmDomainGetMetadata, /* 1.1.3 */
    .domainSetMetadata = sfvmDomainSetMetadata, /* 1.1.3 */
    .domainGetCPUStats = sfvmDomainGetCPUStats, /* 5.6.0 */
    .domainSendProcessSignal = sfvmDomainSendProcessSignal, /* 5.5.0 */
    .connectGetCPUModelNames = sfvmConnectGetCPUModelNames, /* 1.1.3 */
    .domainManagedSave = sfvmDomainManagedSave, /* 1.1.4 */
    .domainHasManagedSaveImage = sfvmDomainHasManagedSaveImage, /* 1.1.4 */
    .domainManagedSaveRemove = sfvmDomainManagedSaveRemove, /* 1.1.4 */
    .domainMemoryStats = sfvmDomainMemoryStats, /* 5.7.0 */
    .domainMemoryPeek = sfvmDomainMemoryPeek, /* 5.4.0 */
    .domainGetBlockInfo = sfvmDomainGetBlockInfo, /* 5.7.0 */
    .domainSetLifecycleAction = sfvmDomainSetLifecycleAction, /* 5.7.0 */

    .domainSnapshotNum = sfvmDomainSnapshotNum, /* 1.1.4 */
    .domainSnapshotListNames = sfvmDomainSnapshotListNames, /* 1.1.4 */
    .domainListAllSnapshots = sfvmDomainListAllSnapshots, /* 1.1.4 */
    .domainSnapshotGetXMLDesc = sfvmDomainSnapshotGetXMLDesc, /* 1.1.4 */
    .domainSnapshotNumChildren = sfvmDomainSnapshotNumChildren, /* 1.1.4 */
    .domainSnapshotListChildrenNames = sfvmDomainSnapshotListChildrenNames, /* 1.1.4 */
    .domainSnapshotListAllChildren = sfvmDomainSnapshotListAllChildren, /* 1.1.4 */
    .domainSnapshotLookupByName = sfvmDomainSnapshotLookupByName, /* 1.1.4 */
    .domainHasCurrentSnapshot = sfvmDomainHasCurrentSnapshot, /* 1.1.4 */
    .domainSnapshotGetParent = sfvmDomainSnapshotGetParent, /* 1.1.4 */
    .domainSnapshotCurrent = sfvmDomainSnapshotCurrent, /* 1.1.4 */
    .domainSnapshotIsCurrent = sfvmDomainSnapshotIsCurrent, /* 1.1.4 */
    .domainSnapshotHasMetadata = sfvmDomainSnapshotHasMetadata, /* 1.1.4 */
    .domainSnapshotCreateXML = sfvmDomainSnapshotCreateXML, /* 1.1.4 */
    .domainRevertToSnapshot = sfvmDomainRevertToSnapshot, /* 1.1.4 */
    .domainSnapshotDelete = sfvmDomainSnapshotDelete, /* 1.1.4 */

    .connectBaselineCPU = sfvmConnectBaselineCPU, /* 1.2.0 */
    .domainCheckpointCreateXML = sfvmDomainCheckpointCreateXML, /* 5.6.0 */
    .domainCheckpointGetXMLDesc = sfvmDomainCheckpointGetXMLDesc, /* 5.6.0 */

    .domainListAllCheckpoints = sfvmDomainListAllCheckpoints, /* 5.6.0 */
    .domainCheckpointListAllChildren = sfvmDomainCheckpointListAllChildren, /* 5.6.0 */
    .domainCheckpointLookupByName = sfvmDomainCheckpointLookupByName, /* 5.6.0 */
    .domainCheckpointGetParent = sfvmDomainCheckpointGetParent, /* 5.6.0 */
    .domainCheckpointDelete = sfvmDomainCheckpointDelete, /* 5.6.0 */
    .domainGetMessages = sfvmDomainGetMessages, /* 7.6.0 */
};

static virNetworkDriver sfvmNetworkDriver = {
    .connectNumOfNetworks = sfvmConnectNumOfNetworks, /* 0.3.2 */
    .connectListNetworks = sfvmConnectListNetworks, /* 0.3.2 */
    .connectNumOfDefinedNetworks = sfvmConnectNumOfDefinedNetworks, /* 0.3.2 */
    .connectListDefinedNetworks = sfvmConnectListDefinedNetworks, /* 0.3.2 */
    .connectListAllNetworks = sfvmConnectListAllNetworks, /* 0.10.2 */
    .connectNetworkEventRegisterAny = sfvmConnectNetworkEventRegisterAny, /* 1.2.1 */
    .connectNetworkEventDeregisterAny = sfvmConnectNetworkEventDeregisterAny, /* 1.2.1 */
    .networkLookupByUUID = sfvmNetworkLookupByUUID, /* 0.3.2 */
    .networkLookupByName = sfvmNetworkLookupByName, /* 0.3.2 */
    .networkCreateXML = sfvmNetworkCreateXML, /* 0.3.2 */
    .networkCreateXMLFlags = sfvmNetworkCreateXMLFlags, /* 7.8.0 */
    .networkDefineXML = sfvmNetworkDefineXML, /* 0.3.2 */
    .networkDefineXMLFlags = sfvmNetworkDefineXMLFlags, /* 7.7.0 */
    .networkUndefine = sfvmNetworkUndefine, /* 0.3.2 */
    .networkUpdate = sfvmNetworkUpdate, /* 0.10.2 */
    .networkCreate = sfvmNetworkCreate, /* 0.3.2 */
    .networkDestroy = sfvmNetworkDestroy, /* 0.3.2 */
    .networkGetXMLDesc = sfvmNetworkGetXMLDesc, /* 0.3.2 */
    .networkGetBridgeName = sfvmNetworkGetBridgeName, /* 0.3.2 */
    .networkGetAutostart = sfvmNetworkGetAutostart, /* 0.3.2 */
    .networkSetAutostart = sfvmNetworkSetAutostart, /* 0.3.2 */
    .networkIsActive = sfvmNetworkIsActive, /* 0.7.3 */
    .networkIsPersistent = sfvmNetworkIsPersistent, /* 0.7.3 */
};

static virInterfaceDriver sfvmInterfaceDriver = {
    .connectNumOfInterfaces = sfvmConnectNumOfInterfaces, /* 0.7.0 */
    .connectListInterfaces = sfvmConnectListInterfaces, /* 0.7.0 */
    .connectNumOfDefinedInterfaces = sfvmConnectNumOfDefinedInterfaces, /* 0.7.0 */
    .connectListDefinedInterfaces = sfvmConnectListDefinedInterfaces, /* 0.7.0 */
    .connectListAllInterfaces = sfvmConnectListAllInterfaces, /* 4.6.0 */
    .interfaceLookupByName = sfvmInterfaceLookupByName, /* 0.7.0 */
    .interfaceLookupByMACString = sfvmInterfaceLookupByMACString, /* 0.7.0 */
    .interfaceGetXMLDesc = sfvmInterfaceGetXMLDesc, /* 0.7.0 */
    .interfaceDefineXML = sfvmInterfaceDefineXML, /* 0.7.0 */
    .interfaceUndefine = sfvmInterfaceUndefine, /* 0.7.0 */
    .interfaceCreate = sfvmInterfaceCreate, /* 0.7.0 */
    .interfaceDestroy = sfvmInterfaceDestroy, /* 0.7.0 */
    .interfaceIsActive = sfvmInterfaceIsActive, /* 0.7.3 */
    .interfaceChangeBegin = sfvmInterfaceChangeBegin,   /* 0.9.2 */
    .interfaceChangeCommit = sfvmInterfaceChangeCommit,  /* 0.9.2 */
    .interfaceChangeRollback = sfvmInterfaceChangeRollback, /* 0.9.2 */
};


static virStorageDriver sfvmStorageDriver = {
    .connectNumOfStoragePools = sfvmConnectNumOfStoragePools, /* 0.5.0 */
    .connectListStoragePools = sfvmConnectListStoragePools, /* 0.5.0 */
    .connectNumOfDefinedStoragePools = sfvmConnectNumOfDefinedStoragePools, /* 0.5.0 */
    .connectListDefinedStoragePools = sfvmConnectListDefinedStoragePools, /* 0.5.0 */
    .connectListAllStoragePools = sfvmConnectListAllStoragePools, /* 0.10.2 */
    .connectFindStoragePoolSources = sfvmConnectFindStoragePoolSources, /* 0.5.0 */
    .connectStoragePoolEventRegisterAny = sfvmConnectStoragePoolEventRegisterAny, /* 2.0.0 */
    .connectStoragePoolEventDeregisterAny = sfvmConnectStoragePoolEventDeregisterAny, /* 2.0.0 */
    .storagePoolLookupByName = sfvmStoragePoolLookupByName, /* 0.5.0 */
    .storagePoolLookupByUUID = sfvmStoragePoolLookupByUUID, /* 0.5.0 */
    .storagePoolLookupByVolume = sfvmStoragePoolLookupByVolume, /* 0.5.0 */
    .storagePoolCreateXML = sfvmStoragePoolCreateXML, /* 0.5.0 */
    .storagePoolDefineXML = sfvmStoragePoolDefineXML, /* 0.5.0 */
    .storagePoolBuild = sfvmStoragePoolBuild, /* 0.5.0 */
    .storagePoolUndefine = sfvmStoragePoolUndefine, /* 0.5.0 */
    .storagePoolCreate = sfvmStoragePoolCreate, /* 0.5.0 */
    .storagePoolDestroy = sfvmStoragePoolDestroy, /* 0.5.0 */
    .storagePoolDelete = sfvmStoragePoolDelete, /* 0.5.0 */
    .storagePoolRefresh = sfvmStoragePoolRefresh, /* 0.5.0 */
    .storagePoolGetInfo = sfvmStoragePoolGetInfo, /* 0.5.0 */
    .storagePoolGetXMLDesc = sfvmStoragePoolGetXMLDesc, /* 0.5.0 */
    .storagePoolGetAutostart = sfvmStoragePoolGetAutostart, /* 0.5.0 */
    .storagePoolSetAutostart = sfvmStoragePoolSetAutostart, /* 0.5.0 */
    .storagePoolNumOfVolumes = sfvmStoragePoolNumOfVolumes, /* 0.5.0 */
    .storagePoolListVolumes = sfvmStoragePoolListVolumes, /* 0.5.0 */
    .storagePoolListAllVolumes = sfvmStoragePoolListAllVolumes, /* 0.10.2 */

    .storageVolLookupByName = sfvmStorageVolLookupByName, /* 0.5.0 */
    .storageVolLookupByKey = sfvmStorageVolLookupByKey, /* 0.5.0 */
    .storageVolLookupByPath = sfvmStorageVolLookupByPath, /* 0.5.0 */
    .storageVolCreateXML = sfvmStorageVolCreateXML, /* 0.5.0 */
    .storageVolCreateXMLFrom = sfvmStorageVolCreateXMLFrom, /* 0.6.4 */
    .storageVolDelete = sfvmStorageVolDelete, /* 0.5.0 */
    .storageVolGetInfo = sfvmStorageVolGetInfo, /* 0.5.0 */
    .storageVolGetXMLDesc = sfvmStorageVolGetXMLDesc, /* 0.5.0 */
    .storageVolGetPath = sfvmStorageVolGetPath, /* 0.5.0 */
    .storagePoolIsActive = sfvmStoragePoolIsActive, /* 0.7.3 */
    .storagePoolIsPersistent = sfvmStoragePoolIsPersistent, /* 0.7.3 */
};

static virNodeDeviceDriver sfvmNodeDeviceDriver = {
    .connectListAllNodeDevices = sfvmConnectListAllNodeDevices, /* 4.1.0 */
    .connectNodeDeviceEventRegisterAny = sfvmConnectNodeDeviceEventRegisterAny, /* 2.2.0 */
    .connectNodeDeviceEventDeregisterAny = sfvmConnectNodeDeviceEventDeregisterAny, /* 2.2.0 */
    .nodeNumOfDevices = sfvmNodeNumOfDevices, /* 0.7.2 */
    .nodeListDevices = sfvmNodeListDevices, /* 0.7.2 */
    .nodeDeviceLookupByName = sfvmNodeDeviceLookupByName, /* 0.7.2 */
    .nodeDeviceGetXMLDesc = sfvmNodeDeviceGetXMLDesc, /* 0.7.2 */
    .nodeDeviceGetParent = sfvmNodeDeviceGetParent, /* 0.7.2 */
    .nodeDeviceNumOfCaps = sfvmNodeDeviceNumOfCaps, /* 0.7.2 */
    .nodeDeviceListCaps = sfvmNodeDeviceListCaps, /* 0.7.2 */
    .nodeDeviceCreateXML = sfvmNodeDeviceCreateXML, /* 0.7.3 */
    .nodeDeviceDestroy = sfvmNodeDeviceDestroy, /* 0.7.3 */
};

static virConnectDriver sfvmConnectDriver = {
    .localOnly = true,
    .uriSchemes = (const char *[]){ "sfvm", NULL },
    .hypervisorDriver = &sfvmHypervisorDriver,
    .interfaceDriver = &sfvmInterfaceDriver,
    .networkDriver = &sfvmNetworkDriver,
    .nodeDeviceDriver = &sfvmNodeDeviceDriver,
    .nwfilterDriver = NULL,
    .secretDriver = NULL,
    .storageDriver = &sfvmStorageDriver,
};

/**
 * sfvmRegister:
 *
 * Registers the sfvm driver
 */
int
sfvmRegister(void)
{
    return virRegisterConnectDriver(&sfvmConnectDriver,
                                    false);
}
