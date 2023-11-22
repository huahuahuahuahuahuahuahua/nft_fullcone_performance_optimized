// SPDX-License-Identifier: GPL-2.0-only
/*
 * Nftables NAT extension: fullcone expression support
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
#define NF_FULLCONE_WORKQUEUE_NAME "fullcone " KBUILD_MODNAME ": wq"

#include <linux/proc_fs.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/module.h>
#include <linux/list.h>
#include <linux/netlink.h>
#include <linux/netfilter.h>
#include <linux/netfilter/nf_tables.h>
#include <net/netfilter/nf_tables.h>
#include <net/netfilter/nf_nat.h>

#include "nf_nat_fullcone.h"

int init_fullcone_procfs(void);

void cleanup_fullcone_procfs(void);

static void nft_fullcone_set_regs(const struct nft_expr* expr, const struct nft_regs* regs,
                                  struct nf_nat_range2* range);

struct nft_fullcone {
    u32 flags;
    u8 sreg_proto_min;
    u8 sreg_proto_max;
};

static const struct nla_policy nft_fullcone_policy[NFTA_FULLCONE_MAX + 1] = {
    [NFTA_FULLCONE_FLAGS] = {.type = NLA_U32},
    [NFTA_FULLCONE_REG_PROTO_MIN] = {.type = NLA_U32},
    [NFTA_FULLCONE_REG_PROTO_MAX] = {.type = NLA_U32},
};

static int nft_fullcone_validate(const struct nft_ctx* ctx, const struct nft_expr* expr, const struct nft_data** data) {
    int err;

    err = nft_chain_validate_dependency(ctx->chain, NFT_CHAIN_T_NAT);
    if (err < 0)
        return err;

    // TODO: check hooks
    return nft_chain_validate_hooks(ctx->chain, (1 << NF_INET_PRE_ROUTING) | (1 << NF_INET_POST_ROUTING));
}


#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 2, 0)
static int nft_fullcone_dump(struct sk_buff *skb, const struct nft_expr *expr, bool reset)
#else
static int nft_fullcone_dump(struct sk_buff* skb, const struct nft_expr* expr)
#endif
{
    const struct nft_fullcone* priv = nft_expr_priv(expr);

    if (priv->flags != 0 && nla_put_be32(skb, NFTA_FULLCONE_FLAGS, htonl(priv->flags)))
        goto nla_put_failure;

    if (priv->sreg_proto_min) {
        if (nft_dump_register(skb, NFTA_FULLCONE_REG_PROTO_MIN,
                              priv->sreg_proto_min) ||
            nft_dump_register(skb, NFTA_FULLCONE_REG_PROTO_MAX, priv->sreg_proto_max))
            goto nla_put_failure;
    }

    return 0;

nla_put_failure:
    return -1;
}

/* nft_fullcone_set_regs sets nft_regs from nft_expr fullcone specific private data */
static void nft_fullcone_set_regs(const struct nft_expr* expr, const struct nft_regs* regs,
                                  struct nf_nat_range2* range
) {
    // private data connected via nft_expr_type.ops <==> nft_expr_ops.type
    // private data type from nft_expr_type.{policy,maxattr,ops}
    // private data size from nft_expr_ops.size
    struct nft_fullcone* priv = nft_expr_priv(expr);
    range->flags = priv->flags;
    if (priv->sreg_proto_min) {
        range->min_proto.all = (__force __be16)
                nft_reg_load16(&regs->data[priv->sreg_proto_min]);
        range->max_proto.all = (__force __be16)
                nft_reg_load16(&regs->data[priv->sreg_proto_max]);
    }
}

static void nft_fullcone_ipv4_eval(const struct nft_expr* expr, struct nft_regs* regs, const struct nft_pktinfo* pkt) {
    struct nf_nat_range2 range;

    memset(&range, 0, sizeof(range));
    nft_fullcone_set_regs(expr, regs, &range);
    regs->verdict.code = nf_nat_fullcone_ipv4(pkt->skb, nft_hook(pkt), &range, nft_out(pkt));
}

static int nft_fullcone_init(const struct nft_ctx* ctx, const struct nft_expr* expr, const struct nlattr* const tb[]) {
    return nf_ct_netns_get(ctx->net, ctx->family);;
}

static void nft_fullcone_common_destory(const struct nft_ctx* ctx){
}

static void nft_fullcone_ipv4_destroy(const struct nft_ctx* ctx, const struct nft_expr* expr) {
    nft_fullcone_common_destory(ctx);
    nf_ct_netns_put(ctx->net, NFPROTO_IPV4);
}

static struct nft_expr_type nft_fullcone_ipv4_type;
static const struct nft_expr_ops nft_fullcone_ipv4_ops = {
    .type = &nft_fullcone_ipv4_type,
    .size = NFT_EXPR_SIZE(sizeof(struct nft_fullcone)),
    .eval = nft_fullcone_ipv4_eval,
    .init = nft_fullcone_init,
    .destroy = nft_fullcone_ipv4_destroy,
    .dump = nft_fullcone_dump,
    .validate = nft_fullcone_validate,
};

static struct nft_expr_type nft_fullcone_ipv4_type __read_mostly = {
    .family = NFPROTO_IPV4,
    .name = "fullcone",
    .ops = &nft_fullcone_ipv4_ops,
    .policy = nft_fullcone_policy,
    .maxattr = NFTA_FULLCONE_MAX,
    .owner = THIS_MODULE,
};

static void nft_fullcone_inet_eval(const struct nft_expr* expr, struct nft_regs* regs, const struct nft_pktinfo* pkt) {
    pr_debug("nft_fullcone_inet_eval");

    switch (nft_pf(pkt)) {
        case NFPROTO_IPV4:
            return nft_fullcone_ipv4_eval(expr, regs, pkt);
    }

    WARN_ON_ONCE(1);
}

static void nft_fullcone_inet_destroy(const struct nft_ctx* ctx, const struct nft_expr* expr) {
    nft_fullcone_common_destory(ctx);
    nf_ct_netns_put(ctx->net, NFPROTO_INET);
}

static struct nft_expr_type nft_fullcone_inet_type;
static const struct nft_expr_ops nft_fullcone_inet_ops = {
    .type = &nft_fullcone_inet_type,
    .size = NFT_EXPR_SIZE(sizeof(struct nft_fullcone)),
    .eval = nft_fullcone_inet_eval,
    .init = nft_fullcone_init,
    .destroy = nft_fullcone_inet_destroy,
    .dump = nft_fullcone_dump,
    .validate = nft_fullcone_validate,
};

static struct nft_expr_type nft_fullcone_inet_type __read_mostly = {
    .family = NFPROTO_INET,
    .name = "fullcone",
    .ops = &nft_fullcone_inet_ops,
    .policy = nft_fullcone_policy,
    .maxattr = NFTA_FULLCONE_MAX,
    .owner = THIS_MODULE,
};

static int __init nft_fullcone_module_init_inet(void) {
    return nft_register_expr(&nft_fullcone_inet_type);
}

static void nft_fullcone_module_exit_inet(void) {
    nft_unregister_expr(&nft_fullcone_inet_type);
}

void nf_nat_fullcone_init_locks(void);

static int __init nft_fullcone_module_init(void) {
    int ret;

    pr_info("nft_fullcone loaded");
    ret = nft_fullcone_module_init_inet();
    if (ret < 0) {
        return ret;
    }

    ret = nft_register_expr(&nft_fullcone_ipv4_type);
    if (ret < 0) {
        nft_fullcone_module_exit_inet();
        return ret;
    }

    nf_nat_fullcone_init_locks();

    init_fullcone_procfs();

    return ret;
}

static void __exit nft_fullcone_module_exit(void) {
    pr_debug("nft_fullcone exit");

    nft_fullcone_module_exit_inet();
    nft_unregister_expr(&nft_fullcone_ipv4_type);
    nf_nat_fullcone_destroy_mappings();

    cleanup_fullcone_procfs();
}

module_init(nft_fullcone_module_init);

module_exit(nft_fullcone_module_exit);

MODULE_LICENSE("GPL");

MODULE_AUTHOR("Syrone Wong <wong.syrone@gmail.com>");

MODULE_ALIAS_NFT_EXPR("fullcone");

MODULE_DESCRIPTION("Netfilter nftables fullcone expression support of RFC3489 full cone NAT");
