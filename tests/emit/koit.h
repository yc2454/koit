/*
 * koit.h: what the C that koitc emits relies on, kept small enough
 * to read in one sitting. The fixed-width types, the BPF section
 * and map-definition macros libbpf uses, the context structs of the
 * kinds stage 1 targets with the field offsets of the uapi header,
 * the helpers the corpus calls at their uapi numbers, and the
 * total-arithmetic shim: division and modulo by zero, the signed
 * corner cases, and shift amounts masked to the width, with exactly
 * the semantics of the BPF instruction set, so that no C undefined
 * behavior is reachable from the emitted code.
 *
 * Every declaration cites the kernel object it transcribes; the
 * helper numbers and struct layouts are include/uapi/linux/bpf.h.
 */
#ifndef KOIT_H
#define KOIT_H

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef signed char s8;
typedef short s16;
typedef int s32;
typedef long long s64;

#define NULL ((void *)0)
#define SEC(name) __attribute__((section(name), used))
#define __uint(name, val) int (*name)[val]
#define __type(name, val) typeof(val) *name
#define __always_inline inline __attribute__((always_inline))
#define __ksym __attribute__((section(".ksyms"))) __attribute__((weak))

/* enum bpf_map_type */
enum {
	BPF_MAP_TYPE_HASH = 1,
	BPF_MAP_TYPE_ARRAY = 2,
	BPF_MAP_TYPE_PERCPU_ARRAY = 6,
	BPF_MAP_TYPE_RINGBUF = 27,
};
#define BPF_ANY 0
#define BPF_F_CURRENT_NETNS (-1L)

/* struct xdp_md */
struct xdp_md {
	u32 data;
	u32 data_end;
	u32 data_meta;
	u32 ingress_ifindex;
	u32 rx_queue_index;
	u32 egress_ifindex;
};

/* struct __sk_buff, up to data_meta; the verifier reads the context
 * by offset, so the layout is the uapi one */
struct __sk_buff {
	u32 len;
	u32 pkt_type;
	u32 mark;
	u32 queue_mapping;
	u32 protocol;
	u32 vlan_present;
	u32 vlan_tci;
	u32 vlan_proto;
	u32 priority;
	u32 ingress_ifindex;
	u32 ifindex;
	u32 tc_index;
	u32 cb[5];
	u32 hash;
	u32 tc_classid;
	u32 data;
	u32 data_end;
	u32 napi_id;
	u32 family;
	u32 remote_ip4;
	u32 local_ip4;
	u32 remote_ip6[4];
	u32 local_ip6[4];
	u32 remote_port;
	u32 local_port;
	u32 data_meta;
};

/* struct bpf_spin_lock */
struct bpf_spin_lock {
	u32 val;
};

/* struct bpf_sock_tuple, the IPv4 member; koit's SockTuple */
struct koit_sock_tuple {
	u32 saddr;
	u32 daddr;
	u16 sport;
	u16 dport;
};

/* the helpers, by their numbers in enum bpf_func_id */
static void *(*bpf_map_lookup_elem)(void *map, const void *key) = (void *)1;
static long (*bpf_map_update_elem)(void *map, const void *key, const void *value,
				   u64 flags) = (void *)2;
static long (*bpf_map_delete_elem)(void *map, const void *key) = (void *)3;
static u64 (*bpf_ktime_get_ns)(void) = (void *)5;
static long (*bpf_trace_printk)(const char *fmt, u32 fmt_size, ...) = (void *)6;
static long (*bpf_redirect)(u32 ifindex, u64 flags) = (void *)23;
static long (*bpf_skb_change_tail)(void *skb, u32 len, u64 flags) = (void *)38;
static long (*bpf_skb_change_head)(void *skb, u32 len, u64 flags) = (void *)43;
static long (*bpf_xdp_adjust_head)(void *xdp, int delta) = (void *)44;
static long (*bpf_xdp_adjust_tail)(void *xdp, int delta) = (void *)65;
static void *(*bpf_sk_lookup_tcp)(void *ctx, void *tuple, u32 tuple_size, u64 netns,
				  u64 flags) = (void *)84;
static void *(*bpf_sk_lookup_udp)(void *ctx, void *tuple, u32 tuple_size, u64 netns,
				  u64 flags) = (void *)85;
static long (*bpf_sk_release)(void *sock) = (void *)86;
static long (*bpf_spin_lock)(void *lock) = (void *)93;
static long (*bpf_spin_unlock)(void *lock) = (void *)94;
static void *(*bpf_ringbuf_reserve)(void *ringbuf, u64 size, u64 flags) = (void *)131;
static void (*bpf_ringbuf_submit)(void *data, u64 flags) = (void *)132;
static void (*bpf_ringbuf_discard)(void *data, u64 flags) = (void *)133;

/* the scope resources' kfuncs */
extern void bpf_rcu_read_lock(void) __ksym;
extern void bpf_rcu_read_unlock(void) __ksym;
extern void bpf_preempt_disable(void) __ksym;
extern void bpf_preempt_enable(void) __ksym;
extern void bpf_local_irq_save(unsigned long *flags) __ksym;
extern void bpf_local_irq_restore(unsigned long *flags) __ksym;

#define bpf_printk(fmt, args...)                                       \
	({                                                             \
		static const char ____fmt[] = fmt;                     \
		bpf_trace_printk(____fmt, sizeof(____fmt), ##args);    \
	})

/*
 * Total arithmetic, section 8.1 of the definition: x / 0 is 0, x % 0
 * is x, MIN / -1 is MIN and MIN % -1 is 0, and a shift masks its
 * amount to the width. Narrow operations are computed at 32 bits
 * and reduced, as the instruction set does.
 */
#define KOIT_UNSIGNED(T, W)                                                    \
	static __always_inline T koit_div_##T(T a, T b) { return b == 0 ? 0 : a / b; } \
	static __always_inline T koit_mod_##T(T a, T b) { return b == 0 ? a : a % b; } \
	static __always_inline T koit_shl_##T(T a, T s) { return (T)((u64)a << (s & (W - 1))); } \
	static __always_inline T koit_shr_##T(T a, T s) { return (T)((u64)a >> (s & (W - 1))); }

#define KOIT_SIGNED(T, U, W, MIN)                                              \
	static __always_inline T koit_div_##T(T a, T b)                        \
	{                                                                      \
		if (b == 0) return 0;                                          \
		if (a == MIN && b == -1) return a;                             \
		return a / b;                                                  \
	}                                                                      \
	static __always_inline T koit_mod_##T(T a, T b)                        \
	{                                                                      \
		if (b == 0) return a;                                          \
		if (a == MIN && b == -1) return 0;                             \
		return a % b;                                                  \
	}                                                                      \
	static __always_inline T koit_shl_##T(T a, T s) { return (T)((u64)(U)a << (s & (W - 1))); } \
	static __always_inline T koit_shr_##T(T a, T s) { return (T)((s64)a >> (s & (W - 1))); }

KOIT_UNSIGNED(u8, 8)
KOIT_UNSIGNED(u16, 16)
KOIT_UNSIGNED(u32, 32)
KOIT_UNSIGNED(u64, 64)
KOIT_SIGNED(s8, u8, 8, (-128))
KOIT_SIGNED(s16, u16, 16, (-32768))
KOIT_SIGNED(s32, u32, 32, (-2147483647 - 1))
KOIT_SIGNED(s64, u64, 64, (-9223372036854775807LL - 1))

/* csum_add and csum_fold of the kernel, include/net/checksum.h */
static __always_inline u32 koit_csum_add(u32 csum, u32 addend)
{
	u32 res = csum + addend;
	return res + (res < addend);
}

static __always_inline u16 koit_csum_fold(u32 csum)
{
	csum = (csum & 0xffff) + (csum >> 16);
	csum = (csum & 0xffff) + (csum >> 16);
	return (u16)~csum;
}

#endif
