/*
 * koit.h: what the C that koitc emits relies on, kept small enough
 * to read in one sitting. The fixed-width types, the BPF section
 * and map-definition macros libbpf uses, the spin lock's struct, the
 * printk macro, and the total-arithmetic shim: division and modulo
 * by zero, the signed corner cases, and shift amounts masked to the
 * width, with exactly the semantics of the BPF instruction set, so
 * that no C undefined behavior is reachable from the emitted code.
 *
 * Nothing the kernel states is written here: the context structs,
 * the helpers at their numbers, and the kfuncs are declared by the
 * emitted unit itself from the kernel side of koit's interface,
 * transcribed from the kernel's sources for the target tag.
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

/* struct bpf_spin_lock, which libbpf's BTF recognizes by name */
struct bpf_spin_lock {
	u32 val;
};

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
