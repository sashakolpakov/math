#include <cfenv>
#include <cfloat>
#include <climits>
#include <clocale>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <type_traits>
#include <xmmintrin.h>
#if !defined(__x86_64__) || !defined(__linux__) || !defined(__GLIBC__)
#error Requires x86-64 GNU/Linux
#endif
#if !defined(__GNUC__) || defined(__clang__) || defined(__INTEL_COMPILER)
#error Requires GNU GCC C++ compiler
#endif
#if defined(__FAST_MATH__) || __FINITE_MATH_ONLY__ != 0
#error Fast math is not permitted
#endif
static_assert(CHAR_BIT == 8 && sizeof(int) == 4, "int32 / byte ABI");
static_assert(sizeof(std::size_t) == 8 && sizeof(void*) == 8, "64-bit ABI");
static_assert(sizeof(std::uint64_t) == 8 && sizeof(unsigned long) == 8, "uint64 ABI");
static_assert(std::is_same<std::uint64_t, unsigned long>::value, "uint64_t is unsigned long");
static_assert(sizeof(double) == 8 && std::numeric_limits<double>::is_iec559 &&
              std::numeric_limits<double>::radix == 2 && std::numeric_limits<double>::digits == 53 &&
              std::numeric_limits<double>::max_exponent == 1024, "IEEE binary64");
static_assert(FLT_EVAL_METHOD == 0, "binary64 intermediates");
int main() {
    if (!std::setlocale(LC_ALL, "C") || std::fesetround(FE_TONEAREST) != 0) return 2;
    const unsigned mxcsr = _mm_getcsr();
    unsigned short x87_control = 0;
    __asm__ volatile("fnstcw %0" : "=m"(x87_control));
    const std::uint64_t one = 1;
    const bool little = *reinterpret_cast<const unsigned char*>(&one) == 1;
    const bool mode = !(mxcsr & ((1u << 15) | (1u << 6) | (3u << 13))) &&
                      (mxcsr & (63u << 7)) == (63u << 7);
    const bool x87_mode = !(x87_control & (3u << 10)) && (x87_control & 63u) == 63u;
    volatile double minimum = std::numeric_limits<double>::min();
    volatile double subnormal = std::numeric_limits<double>::denorm_min();
    volatile double two = 2.;
    volatile double half_minimum = minimum / two;
    volatile double twice_subnormal = subnormal * two;
    volatile double square_root = std::sqrt(two);
    const bool gradual = half_minimum == 0x0.8p-1022 && twice_subnormal == 0x0.0000000000002p-1022;
    const bool sqrt_sample = square_root == 0x1.6a09e667f3bcdp+0;
    const bool nearest = std::fegetround() == FE_TONEAREST;
    const bool ok = little && mode && x87_mode && gradual && sqrt_sample && nearest;
    std::puts(ok ? "arithmetic/ABI checks passed" : "arithmetic/ABI checks failed");
    return ok ? 0 : 3;
}
