#include <stdint.h>

typedef uintptr_t __u64;

uintptr_t swab(uintptr_t x) {
  uintptr_t ret;
  ret = ((__u64)(         
        (((__u64)(x) & (__u64)0x00000000000000ffULL) << 56) | 
        (((__u64)(x) & (__u64)0x000000000000ff00ULL) << 40) |
        (((__u64)(x) & (__u64)0x0000000000ff0000ULL) << 24) |
        (((__u64)(x) & (__u64)0x00000000ff000000ULL) <<  8) |
        (((__u64)(x) & (__u64)0x000000ff00000000ULL) >>  8) |
        (((__u64)(x) & (__u64)0x0000ff0000000000ULL) >> 24) |
        (((__u64)(x) & (__u64)0x00ff000000000000ULL) >> 40) |
        (((__u64)(x) & (__u64)0xff00000000000000ULL) >> 56)));
  return ret;
}
/* #define swab(x) ((__u64)(                              \ */
/*         (((__u64)(x) & (__u64)0x00000000000000ffULL) << 56) |        \ */
/*         (((__u64)(x) & (__u64)0x000000000000ff00ULL) << 40) |        \ */
/*         (((__u64)(x) & (__u64)0x0000000000ff0000ULL) << 24) |        \ */
/*         (((__u64)(x) & (__u64)0x00000000ff000000ULL) <<  8) |        \ */
/*         (((__u64)(x) & (__u64)0x000000ff00000000ULL) >>  8) |        \ */
/*         (((__u64)(x) & (__u64)0x0000ff0000000000ULL) >> 24) |        \ */
/*         (((__u64)(x) & (__u64)0x00ff000000000000ULL) >> 40) |        \ */
/*         (((__u64)(x) & (__u64)0xff00000000000000ULL) >> 56))) */

uintptr_t encode(uintptr_t key, void *ptr, uintptr_t ptr_addr) {
  uintptr_t encoded;
  encoded = (uintptr_t)ptr ^ key ^ swab(ptr_addr);
  return encoded;
}

void *decode(uintptr_t key, uintptr_t ptr, uintptr_t ptr_addr) {
  void *decoded;
  decoded = (void *)(ptr ^ key ^ swab(ptr_addr));
  return decoded;
}

long bar(uintptr_t key, uintptr_t ptr, uintptr_t ptr_addr) {
  long *q = decode(key, ptr, ptr_addr);
  return *q;
}

long foo(uintptr_t key, uintptr_t ptr_addr) {
  long *p;
  *p = 42;
  uintptr_t qi = encode(key, p, ptr_addr);
  long ret = bar(key, qi, ptr_addr);
  return ret;
}
// *q == 42
