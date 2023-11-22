// SPDX-License-Identifier: GPL-2.0-only

/*
 * Nftables NAT extension: fullcone expression support library
 *
 * Copyright (c) 2018 Chion Tang <tech@chionlab.moe>
 *   Original xt_FULLCONENAT and related iptables extension author
 * Copyright (c) 2019-2022 GitHub/llccd Twitter/@gNodeB
 *   Added IPv6 support for xt_FULLCONENAT and ip6tables extension
 *   Ported to recent kernel versions
 * Copyright (c) 2022 Syrone Wong <wong.syrone@gmail.com>
 *   Massively rewrite the whole module, split the original code into library and nftables 'fullcone' expression module
 */

#define pr_fmt(fmt) "fullcone " KBUILD_MODNAME ": " fmt

#include <linux/version.h>
#include <linux/types.h>
#include <linux/list.h>
#include <linux/hashtable.h>
#include <linux/atomic.h>
#include <linux/kernel.h>
#include <linux/jhash.h>
#include <linux/ktime.h>
#include <linux/mm.h>
#include <linux/proc_fs.h>

#ifdef CONFIG_NF_CONNTRACK_CHAIN_EVENTS
#include <linux/notifier.h>
#endif

#include <linux/netfilter.h>
#include <linux/netfilter_ipv4.h>

#include "nf_nat_fullcone.h"

/*
 * FULLCONE_HKEY generates u32 hash value
 * Modified from net/netfilter/ipset/ip_set_hash_gen.h
 * dataptr: a pointer
 * datatypelen: sizeof(struct blah) or sizeof(u32)
 * initval: initial value
 * htable_bits: hashtable bits
 */
#define FULLCONE_HKEY(dataptr, datatypelen, initval, htable_bits)			\
({								\
const u32 *__k = (const u32 *)(dataptr);			\
u32 __l = (datatypelen) / sizeof(u32);			\
\
BUILD_BUG_ON((datatypelen) % sizeof(u32) != 0);		\
\
jhash2(__k, __l, (initval)) & jhash_mask((htable_bits));	\
})

static __u64 allocated;
static __u64 released;
static DEFINE_SPINLOCK(stats_lock);

/* static variables */

static DEFINE_HASHTABLE(mapping_table_by_ext_port, HASHTABLE_BUCKET_BITS);

static DEFINE_HASHTABLE(mapping_table_by_int_src, HASHTABLE_BUCKET_BITS);

static spinlock_t ext_mapping_locks[sizeof(mapping_table_by_ext_port) / sizeof(mapping_table_by_ext_port[0])];
static spinlock_t int_mapping_locks[sizeof(mapping_table_by_int_src) / sizeof(mapping_table_by_int_src[0])];


static void kill_mapping(struct nat_mapping* mapping);

static __be32 find_leastused_ip(struct nf_nat_range2* range,
                                const __be32 src, const __be32 dst);

/* forward declaration end */

static void kill_mapping(struct nat_mapping* mapping) {
    if (mapping == NULL) {
        return;
    }

    hash_del(&mapping->node_by_ext_port);
    hash_del(&mapping->node_by_int_src);
    kfree(mapping);
}

static __be16 try_allocate_mapping(const __be32 int_addr, const __be16 original_port, const __be32 ext_ip,
                                   struct nf_nat_range2* range) {
    uint16_t min, selected, range_size, i;
    uint16_t random_port;
    struct nat_mapping* p_new;

    __be16 wan_src_port = 0;

    struct nat_mapping* mapping = NULL;

    struct nat_mapping* p_current;
    struct hlist_node* tmp;
    u32 hash_ext, hash_src;
    spinlock_t* ext_lock = NULL;

    min = 20000;
    range_size = 65535 - min + 1;

    //pr_debug("original port %d", __be16_to_cpu(original_port));

    if (__be16_to_cpu(original_port) >= 1024 && __be16_to_cpu(original_port) <= 65534) {
        hash_ext = FULLCONE_HKEY(&ext_ip, sizeof(__be32), (u32) original_port, HASHTABLE_BUCKET_BITS);
        ext_lock = &ext_mapping_locks[hash_min(hash_ext, HASH_BITS(mapping_table_by_ext_port))];
        spin_lock_bh(ext_lock);
        hash_for_each_possible_safe(mapping_table_by_ext_port, p_current, tmp, node_by_ext_port, hash_ext) {
            if (p_current->port == original_port && p_current->addr == ext_ip) {
                mapping = p_current;
                break;
            }
        }
        if (mapping) {
            pr_debug("mapping %pI4:%d already existing", &ext_ip, __be16_to_cpu(original_port));
            spin_unlock_bh(ext_lock);
            goto allocate;
        }
        wan_src_port = original_port;
        //  pr_debug("original port %d is available", __be16_to_cpu(original_port));
        goto add_mapping;
    }

allocate:
#define MAX_RETRY 20
    for (i = 0; i < MAX_RETRY; i++) {
        wan_src_port = 0;
        /* 2. try to find an available port */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 1, 0)
            random_port = (uint16_t) (get_random_u32() % (u32) range_size);
#else
        random_port = (uint16_t)(prandom_u32() % (u32)range_size);
#endif
        selected = __cpu_to_be16(min + (random_port) % range_size);

        hash_ext = FULLCONE_HKEY(&ext_ip, sizeof(__be32), (u32) selected, HASHTABLE_BUCKET_BITS);
        ext_lock = &ext_mapping_locks[hash_min(hash_ext, HASH_BITS(mapping_table_by_ext_port))];
        mapping = NULL;
        spin_lock_bh(ext_lock);
        hash_for_each_possible_safe(mapping_table_by_ext_port, p_current, tmp, node_by_ext_port, hash_ext) {
            if (p_current->port == selected && p_current->addr == ext_ip) {
                mapping = p_current;
                break;
            }
        }
        if (mapping != NULL) {
            pr_debug("select port %d failed mapping %p", selected, mapping);
            spin_unlock_bh(ext_lock);
            continue;
        }
        wan_src_port = selected;
        break;
    }

add_mapping:
    if (wan_src_port == 0) {
        pr_debug("allocate mapping for %pI4:%d failed", &int_addr, original_port);
        return 0;
    }

    p_new = kmalloc(sizeof(struct nat_mapping), GFP_ATOMIC);
    if (p_new == NULL) {
        pr_err("kmalloc() for allocate_mapping failed.\n");
        goto unlock;
    }
    p_new->addr = ext_ip;
    p_new->port = wan_src_port;
    p_new->int_addr = int_addr;
    p_new->int_port = original_port;

    hash_src = FULLCONE_HKEY(&int_addr, sizeof(__be32), (__be32) original_port, HASHTABLE_BUCKET_BITS);
    hash_ext = FULLCONE_HKEY(&ext_ip, sizeof(__be32), (__be32) wan_src_port, HASHTABLE_BUCKET_BITS);

    hash_add(mapping_table_by_ext_port, &p_new->node_by_ext_port, hash_ext);
    hash_add(mapping_table_by_int_src, &p_new->node_by_int_src, hash_src);

    pr_debug("new mapping allocated for OriginSrcIP:Port %pI4:%d ==> WanIP:SrcPort %pI4:%d\n",
             &p_new->int_addr, __cpu_to_be16(p_new->int_port), &p_new->addr, __cpu_to_be16(p_new->port));

unlock:
    spin_unlock_bh(ext_lock);

    return wan_src_port;
}

static __be32 find_leastused_ip(struct nf_nat_range2* range,
                                const __be32 src, const __be32 dst) {
    /* Host order */
    u32 minip, maxip, j, dist;

    // nf_nat_range2 specific
    memset(&(range->base_proto), 0, sizeof(range->base_proto));

    j = FULLCONE_HKEY(&src, sizeof(__be32), 0, HASHTABLE_BUCKET_BITS);

    minip = ntohl(range->min_addr.ip);
    maxip = ntohl(range->max_addr.ip);
    dist = maxip - minip + 1;

    return (__be32)htonl(minip + reciprocal_scale(j, dist));
}

void nf_nat_fullcone_destroy_mappings(void) {
    struct nat_mapping* p_current;
    struct hlist_node* tmp;
    int i;

    hash_for_each_safe(mapping_table_by_ext_port, i, tmp, p_current, node_by_ext_port) {
        kill_mapping(p_current);
    }
}

EXPORT_SYMBOL_GPL(nf_nat_fullcone_destroy_mappings);

/*
 * nfproto choices
 * enum {
	NFPROTO_INET   =  1,
	NFPROTO_IPV4   =  2,
	NFPROTO_IPV6   = 10,
};
 */
static unsigned int nf_nat_handle_prerouting(u8 nfproto, struct sk_buff* skb, unsigned int hooknum,
                                             struct nf_nat_range2* newrange) {
    struct nf_conn* ct;
    enum ip_conntrack_info ctinfo;
    struct nf_conntrack_tuple* ct_tuple_origin;

    uint16_t port = 0;
    uint8_t protonum;

    unsigned int ret;
    __be32 ip;

    struct nat_mapping* mapping = NULL;

    ret = NFT_CONTINUE;

    WARN_ON(!(nfproto == NFPROTO_IPV4 || nfproto == NFPROTO_IPV6));

    if (nfproto != NFPROTO_IPV4) {
        return NF_DROP;
    }

    //pr_debug("nf_nat_handle_prerouting \n");

    ct = nf_ct_get(skb, &ctinfo);
    ct_tuple_origin = &(ct->tuplehash[IP_CT_DIR_ORIGINAL].tuple);
    protonum = (ct_tuple_origin->dst).protonum;
    if (protonum != IPPROTO_UDP || nfproto != NFPROTO_IPV4) {
        // Currently only UDP traffic is supported for full-cone NAT.
        // For other protos FULLCONENAT is equivalent to MASQUERADE.
        return ret;
    }

    ip = (ct_tuple_origin->dst).u3.ip;
    port = (ct_tuple_origin->dst).u.udp.port;

    if (1) {
        struct nat_mapping* p_current;
        struct hlist_node* tmp;
        spinlock_t* lock_ext;

        u32 hash_dst = FULLCONE_HKEY(&ip, sizeof(__be32), (u32) port, HASHTABLE_BUCKET_BITS);
        lock_ext = &ext_mapping_locks[hash_min(hash_dst, HASH_BITS(mapping_table_by_ext_port))];

        spin_lock_bh(lock_ext);
        hash_for_each_possible_safe(mapping_table_by_ext_port, p_current, tmp, node_by_ext_port, hash_dst) {
            if (p_current->port == port && p_current->addr == ip) {
                mapping = p_current;
                break;
            }
        }
        if (mapping == NULL) {
            pr_debug("<INBOUND DNAT> No mapping found for IP %pI4:%d", &ip, __be16_to_cpu(port));
            spin_unlock_bh(lock_ext);
            return ret;
        }
        newrange->flags = NF_NAT_RANGE_MAP_IPS | NF_NAT_RANGE_PROTO_SPECIFIED;
        newrange->min_addr.ip = mapping->int_addr;
        newrange->max_addr.ip = mapping->int_addr;
        newrange->min_proto.udp.port = mapping->int_port;
        newrange->max_proto = newrange->min_proto;

        // pr_debug("<INBOUND DNAT> %s ==> %pI4:%d\n",
        //          nf_ct_stringify_tuple(ct_tuple_origin), &mapping->int_addr, __be16_to_cpu(mapping->int_port));

        ret = nf_nat_setup_info(ct, newrange, HOOK2MANIP(hooknum));
        spin_unlock_bh(lock_ext);
    }

    return ret;
}

static unsigned int nf_nat_handle_postrouting(u8 nfproto, struct sk_buff* skb, unsigned int hooknum,
                                              struct nf_nat_range2* range, struct nf_nat_range2* newrange,
                                              const struct net_device* out) {
    unsigned int ret;
    struct nf_conn* ct;
    enum ip_conntrack_info ctinfo;
    struct nf_conntrack_tuple* ct_tuple_origin;
    uint16_t original_port, allocated_port;
    uint8_t protonum;
    u32 hash_src;

    /* NFPROTO specific def */
    struct nat_mapping* src_mapping;

    __be32 ip;

    const struct rtable* rt;
    __be32 wanip, nh;

    //pr_debug("nf_nat_handle_postrouting");

    /* NFPROTO specific def end */

    WARN_ON(!(nfproto == NFPROTO_IPV4 || nfproto == NFPROTO_IPV6));

    if (nfproto == NFPROTO_IPV6) {
        return NF_DROP;
    }

    /* NFPROTO specific init */
    src_mapping = NULL;

    ip = 0;
    /* NFPROTO specific init end */

    original_port = 0;
    ret = NFT_CONTINUE; // BUG: use XT_CONTINUE for Xtables

    ct = nf_ct_get(skb, &ctinfo);
    if (ct == NULL) {
        pr_err("NULL CT info");
        return NFT_CONTINUE;
    }

    ct_tuple_origin = &(ct->tuplehash[IP_CT_DIR_ORIGINAL].tuple);
    protonum = (ct_tuple_origin->dst).protonum;

    if (range->flags & NF_NAT_RANGE_MAP_IPS) {
        newrange->min_addr.ip = range->min_addr.ip;
        newrange->max_addr.ip = range->min_addr.ip;
    }
    else {
        rt = skb_rtable(skb);
        nh = rt_nexthop(rt, ip_hdr(skb)->daddr);
        wanip = inet_select_addr(out, nh, RT_SCOPE_UNIVERSE);

        if (unlikely(!wanip))
            return NF_DROP;
        newrange->min_addr.ip = wanip;
        newrange->max_addr.ip = wanip;
    }

    if (protonum == IPPROTO_UDP) {
        spinlock_t* lock_src;
        int bucket_idx = 0;
        struct nat_mapping* p_current = NULL;

        ip = (ct_tuple_origin->src).u3.ip;
        original_port = (ct_tuple_origin->src).u.udp.port;

        pr_debug("postrouting %pI4:%d -> %pI4:%d", &ip, __be16_to_cpu(original_port),
                 &(ct_tuple_origin->dst).u3.ip, __be16_to_cpu((ct_tuple_origin->dst).u.udp.port));

        hash_src = FULLCONE_HKEY(&ip, sizeof(__be32), (u32) original_port, HASHTABLE_BUCKET_BITS);
        bucket_idx = hash_min(hash_src, HASH_BITS(mapping_table_by_int_src));
        lock_src = &int_mapping_locks[bucket_idx];
        spin_lock_bh(lock_src);

        hlist_for_each_entry(p_current, &mapping_table_by_int_src[bucket_idx], node_by_int_src) {
            if (p_current->int_addr == ip && p_current->int_port == original_port && p_current->addr == newrange->
                min_addr.ip) {
                src_mapping = p_current;
                break;
            }
        }

        if (src_mapping != NULL) {
            /* outbound nat: if a previously established mapping is active,
             * we will reuse that mapping. */
            newrange->flags = NF_NAT_RANGE_MAP_IPS | NF_NAT_RANGE_PROTO_SPECIFIED;
            newrange->min_proto.udp.port = src_mapping->port;
            newrange->max_proto = newrange->min_proto;
            if (newrange->min_addr.ip != newrange->max_addr.ip) {
                newrange->min_addr.ip = src_mapping->addr;
                newrange->max_addr.ip = newrange->min_addr.ip;
            }
            pr_debug(" %pI4:%d find a mapping", &ip, __be16_to_cpu(original_port));
        }
        else {
            /* if not, we find a new external IP:port to map to.
             * the SNAT may fail so we should re-check the mapped port later. */

            if (newrange->min_addr.ip != newrange->max_addr.ip) {
                newrange->min_addr.ip =
                        find_leastused_ip(range, ip, (ct_tuple_origin->dst).u3.ip);
                newrange->max_addr.ip = newrange->min_addr.ip;
            }

            allocated_port = try_allocate_mapping(ip, original_port, newrange->min_addr.ip, newrange);
            if (allocated_port == 0) {
                pr_debug("allocate mapping failed");
                spin_unlock_bh(lock_src);
                return NF_DROP;
            }
            spin_lock_bh(&stats_lock);
            allocated++;
            spin_unlock_bh(&stats_lock);
            newrange->flags = NF_NAT_RANGE_MAP_IPS | NF_NAT_RANGE_PROTO_SPECIFIED;
            newrange->min_proto.udp.port = allocated_port;
            newrange->max_proto = newrange->min_proto;
        }
        pr_debug("b nat reply %pI4:%d allocate port %d %pI4:%d", &ip, __be16_to_cpu(original_port),
                 __be16_to_cpu(newrange->min_proto.udp.port),
                 &ct_tuple_origin->dst.u3.ip,
                 __be16_to_cpu(ct_tuple_origin->dst.u.udp.port));
        ret = nf_nat_setup_info(ct, newrange, HOOK2MANIP(hooknum));
        ct_tuple_origin = &(ct->tuplehash[IP_CT_DIR_REPLY].tuple);
        pr_debug("a nat ret %pI4:%d reply %pI4:%d", &ip, __be16_to_cpu(original_port), &ct_tuple_origin->dst.u3.ip,
                 __be16_to_cpu(ct_tuple_origin->dst.u.udp.port));
        spin_unlock_bh(lock_src);
    }
    else {
        ret = nf_nat_setup_info(ct, newrange, HOOK2MANIP(hooknum));
    }

    return ret;
}

unsigned int nf_nat_fullcone_ipv4(struct sk_buff* skb, unsigned int hooknum,
                                  struct nf_nat_range2* range,
                                  const struct net_device* out) {
    struct nf_nat_range2 newrange;

    WARN_ON(!(hooknum == NF_INET_POST_ROUTING || hooknum == NF_INET_PRE_ROUTING));

    memset(&newrange.min_addr, 0, sizeof(newrange.min_addr));
    memset(&newrange.max_addr, 0, sizeof(newrange.max_addr));
    newrange.flags = range->flags | NF_NAT_RANGE_MAP_IPS;
    newrange.min_proto = range->min_proto;
    newrange.max_proto = range->max_proto;

    switch (hooknum) {
        case NF_INET_PRE_ROUTING:
            /* inbound packets */
            return nf_nat_handle_prerouting(NFPROTO_IPV4, skb, hooknum, &newrange);
        case NF_INET_POST_ROUTING:
            /* outbound packets */
            return nf_nat_handle_postrouting(NFPROTO_IPV4, skb, hooknum, range, &newrange, out);
    }

    WARN_ON(1);
    // logical error
    return 5;
}

void nf_nat_fullcone_init_locks(void) {
    int i;
    for (i = 0; i < sizeof(ext_mapping_locks) / sizeof(ext_mapping_locks[0]); i++) {
        spin_lock_init(&ext_mapping_locks[i]);
        spin_lock_init(&int_mapping_locks[i]);
    }
}

static struct proc_dir_entry *fullcone_dir = NULL, *mapping_file = NULL, *remove_mapping_file = NULL;

struct mapping {
    __be16 port; /* external source port */
    __be16 int_port; /* internal source port */
    __be32 addr; /* external source ip address */
    __be32 int_addr; /* internal source ip address */
};

#define CONTEXT_MAPPING_COUNT 4096

struct seq_context {
    int count;
    int total;
    int printed;
    struct mapping mappings[CONTEXT_MAPPING_COUNT];
};

static void* mapping_seq_start(struct seq_file* seq, loff_t* pos) {
    struct seq_context* ctx;
    if (*pos == 0) {
        seq_printf(seq, "allocated: %lld released: %lld \n", allocated, released);
    }
    ctx = kmalloc(sizeof(struct seq_context), GFP_KERNEL);
    if (ctx != NULL) {
        return ctx;
    }
    return NULL;
}

static void* mapping_seq_next(struct seq_file* seq, void* v, loff_t* pos) {
    spinlock_t* lock;
    struct hlist_head* bucket;
    struct nat_mapping* p_current = NULL;
    struct seq_context* ctx = v;
    struct mapping* m = NULL;
    int idx = *pos;

    (*pos)++;

    ctx->count = 0;
    if (idx >= (sizeof(mapping_table_by_ext_port) / sizeof(mapping_table_by_ext_port[0]))) {
        return NULL;
    }

    lock = &ext_mapping_locks[idx];
    spin_lock(lock);
    bucket = &mapping_table_by_ext_port[idx];
    hlist_for_each_entry(p_current, bucket, node_by_ext_port) {
        if (ctx->count >= (CONTEXT_MAPPING_COUNT - 1)) {
            pr_err("get more than %d mappings in a bucket", CONTEXT_MAPPING_COUNT);
            goto unlock;
        }
        m = &ctx->mappings[ctx->count];
        m->addr = p_current->addr;
        m->int_addr = p_current->int_addr;
        m->port = p_current->port;
        m->int_port = p_current->int_port;
        ctx->count++;
    }
unlock:
    spin_unlock(lock);
    ctx->total += ctx->count;

    return ctx;
}

static int maping_seq_show(struct seq_file* seq, void* v) {
    int i;
    struct seq_context* ctx = v;
    if (ctx != NULL) {
        for (i = 0; i < ctx->count; i++) {
            struct mapping* m = &ctx->mappings[i];
            seq_printf(seq, "%pI4:%d-%pI4:%d\n",
                       &m->int_addr, __be16_to_cpu(m->int_port),
                       &m->addr, __be16_to_cpu(m->port));
        }
    }
    return 0;
}

static void mapping_seq_stop(struct seq_file* seq, void* v) {
    if (v != NULL) {
        kfree(v);
    }
}

static const struct seq_operations mapping_seq_ops = {
    .start = mapping_seq_start,
    .next = mapping_seq_next,
    .stop = mapping_seq_stop,
    .show = maping_seq_show,
};

static __be16 parse_port(char* in, int len) {
    __u32 port_tmp = 0;
    char c;
    int i, j = 0;
    for (i = 0; i < len; i++) {
        c = in[i];
        if (c == '\0') {
            break;
        }
        if (c == 0) {
            break;
        }
        j = c - '0';
        if (c < '0' || c > '9') {
            pr_err("invalid port %s", in);
            return 0;
        }
        port_tmp = port_tmp * 10 + (c - '0');
    }

    if (port_tmp > 65535) {
        pr_err("invalid port %d", port_tmp);
        return 0;
    }
    return __be16_to_cpu(port_tmp);
}

static __be32 parse_ip(char* in, int len) {
    char c;
    __be32 ip = 0;
    __u16 ip_tmp = 0;
    int i, j;
    j = 0;

    for (i = 0; i < len; i++) {
        c = in[i];
        if (c == '.') {
            if (ip_tmp > 255) {
                pr_err("invalid ip %s", in);
                return 0;
            }
            ip = ip << 8;
            ip = (ip & 0xffffff00) | (ip_tmp & 0x00ff);
            j++;
            ip_tmp = 0;

            continue;
        }
        if (c == '\0') {
            break;
        }
        if (c == 0) {
            break;
        }
        if (c < '0' || c > '9') {
            pr_err("invalid ip %s", in);
            return 0;
        }
        ip_tmp = ip_tmp * 10 + (c - '0');
    }
    if (j != 3) {
        pr_err("invalid ip %s", in);
        return 0;
    }
    ip = ip << 8;
    ip = (ip & 0xffffff00) | (ip_tmp & 0x00ff);
    ip = __cpu_to_be32(ip);

    return ip;
}

static ssize_t remove_mapping_proc_write(struct file* file,
                                         const char __user * buffer, size_t count, loff_t* pos) {
    char int_ip_str[16] = {};
    char ext_ip_str[16] = {};
    char int_port_str[6] = {};
    char ext_port_str[6] = {};
    int end = 0;
    __be32 int_ip = 0, ext_ip = 0;
    __be16 int_port = 0, ext_port = 0;

    int tmp = 0;
    int i, j, separator_idx = 0;
    int ret = count;
    char* buf;

    buf = memdup_user_nul(buffer, count);
    if (IS_ERR(buf)) {
        ret = -EINVAL;
        goto free_buf;
    }

    memset(int_ip_str, '\0', sizeof(int_ip_str));
    memset(int_port_str, '\0', sizeof(int_port_str));
    memset(ext_ip_str, '\0', sizeof(ext_ip_str));
    memset(ext_port_str, '\0', sizeof(ext_port_str));
    for (i = 0; i < count; i++) {
        if (buf[i] == '-') {
            separator_idx = i;
            break;
        }
    }
    if (separator_idx == 0) {
        ret = -EINVAL;
        goto free_buf;
    }

    for (i = 0; i < separator_idx; i++) {
        if (buf[i] == ':') {
            for (j = 0; j < i; j++) {
                int_ip_str[j] = buf[j];
            }
            end = separator_idx;
            if (end > i + 6) {
                end = i + 6;
            }
            for (j = i + 1; j < end; j++) {
                tmp = j - i - 1;
                int_port_str[tmp] = buf[j];
            }
            break;
        }
    }
    int_ip = parse_ip(int_ip_str, sizeof(int_ip_str));
    int_port = parse_port(int_port_str, sizeof(int_port_str));

    for (i = separator_idx + 1; i < count; i++) {
        if (buf[i] == ':') {
            for (j = separator_idx + 1; j < i; j++) {
                ext_ip_str[j - separator_idx - 1] = buf[j];
            }
            end = count - 1;
            if (end > i + 6) {
                end = i + 6;
            }
            for (j = i + 1; j < end; j++) {
                ext_port_str[j - i - 1] = buf[j];
            }
            break;
        }
    }
    ext_ip = parse_ip(ext_ip_str, sizeof(ext_ip_str));
    ext_port = parse_port(ext_port_str, sizeof(ext_port_str));

    pr_debug("raw %s:%s -> %s:%s,parsed %pI4:%d -> %pI4:%d\n",
             int_ip_str, int_port_str, ext_ip_str, ext_port_str,
             &int_ip, __be16_to_cpu(int_port),
             &ext_ip, __be16_to_cpu(ext_port));

    if (1) {
        spinlock_t *lock_src, *lock_ext;
        __u32 hash_src, hash_ext;
        struct nat_mapping *p_current, *found = NULL;
        hash_src = FULLCONE_HKEY(&int_ip, sizeof(__be32), (u32) int_port, HASHTABLE_BUCKET_BITS);
        hash_ext = FULLCONE_HKEY(&ext_ip, sizeof(__be32), (u32) ext_port, HASHTABLE_BUCKET_BITS);
        lock_src = &int_mapping_locks[hash_min(hash_src, HASH_BITS(mapping_table_by_int_src))];
        lock_ext = &ext_mapping_locks[hash_min(hash_ext, HASH_BITS(mapping_table_by_ext_port))];
        spin_lock(lock_src);

        hash_for_each_possible(mapping_table_by_int_src, p_current, node_by_int_src, hash_src) {
            pr_debug("match %pI4:%d -> %pI4:%d",
                     &p_current->int_addr, __be16_to_cpu(p_current->int_port),
                     &p_current->addr, __be16_to_cpu(p_current->port));

            if (p_current->int_addr == int_ip && p_current->int_port == int_port &&
                p_current->addr == ext_ip && p_current->port == ext_port) {
                found = p_current;
                break;
            }
        }
        if (found == NULL) {
            pr_err("could not find mapping %pI4:%d -> %pI4:%d\n",
                   &int_ip, __be16_to_cpu(int_port),
                   &ext_ip, __be16_to_cpu(ext_port));
            spin_unlock(lock_src);
            ret = -EINVAL;
            goto free_buf;
        }
        spin_lock_bh(&stats_lock);
        released++;
        spin_unlock_bh(&stats_lock);
        pr_debug("releasing mapping %pI4:%d -> %pI4:%d",
                 &int_ip, __be16_to_cpu(int_port),
                 &ext_ip, __be16_to_cpu(ext_port));
        hash_del(&found->node_by_int_src);
        spin_unlock(lock_src);

        spin_lock(lock_ext);
        hash_del(&found->node_by_ext_port);
        spin_unlock(lock_ext);

        kfree(found);
    }

free_buf:
    kfree(buf);

    return ret;
}

static const struct proc_ops remove_mapping_proc_ops = {
    .proc_write = remove_mapping_proc_write,
};

int init_fullcone_procfs(void) {
    int rv = 0;
    fullcone_dir = proc_mkdir("nf_fullcone", NULL);
    if (fullcone_dir == NULL) {
        rv = -ENOMEM;
        pr_err("create proc dir failed");
        goto out;
    }

    mapping_file = proc_create_seq_data("mappings", 0444, fullcone_dir, &mapping_seq_ops, NULL);
    if (mapping_file == NULL) {
        rv = -ENOMEM;
        pr_err("create proc mappings file failed");
        goto remove_fullcone_dir;
    }

    remove_mapping_file = proc_create_data("remove_mapping", 0644, fullcone_dir, &remove_mapping_proc_ops, NULL);
    if (remove_mapping_file == NULL) {
        rv = -ENOMEM;
        pr_err("create proc remove_mapping_file failed");
        goto clean_mapping_file;
    }

    goto out;

clean_mapping_file:
    remove_proc_entry("mappings", fullcone_dir);

remove_fullcone_dir:
    remove_proc_entry("nf_fullcone", NULL);

out:
    return rv;
}

void cleanup_fullcone_procfs(void) {
    if (mapping_file != NULL) {
        remove_proc_entry("mappings", fullcone_dir);
    }
    if (remove_mapping_file != NULL) {
        remove_proc_entry("remove_mapping", fullcone_dir);
    }
    if (fullcone_dir != NULL) {
        remove_proc_entry("nf_fullcone", NULL);
    }
}

EXPORT_SYMBOL_GPL(nf_nat_fullcone_ipv4);
