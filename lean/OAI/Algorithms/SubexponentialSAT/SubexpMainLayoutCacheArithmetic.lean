import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCacheBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLagrangeCache

namespace OAI.Algorithms

/-! Fixed polynomial majorants for the actual cache and Lagrange programs.
The argument is deliberately coarse; all exponents and constants are fixed. -/

namespace SubexponentialSAT.SubexpMainLayoutCacheArithmetic

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLiftRing SubexpQuarticRing

def constant : ℕ := 100000000000000000000
def stage (S : ℕ) : ℕ := constant * (S + 1)^8
def grow (S : ℕ) : ℕ := S + stage S + 1
def iterate : ℕ → ℕ → ℕ
  | 0, S => S
  | n + 1, S => grow (iterate n S)

theorem le_grow (S : ℕ) : S ≤ grow S := by unfold grow; omega

theorem selector_le (p input old S : ℕ) (hp : p ≤ S)
    (hb : SubexpEnumerationPayload.scalarWidth p ≤ S) (hi : input ≤ S) (ho : old ≤ S) :
    SubexpQuarticSelectorAdapter.bound p input old ≤ stage S := by
  apply (SubexpQuarticSelectorAdapter.bound_le p input old).trans
  calc
    _ ≤ 16 * S + 2 * S + 200000 * (S + 1)^6 * (S + 1)^2 + 24 * S + 29 := by gcongr
    _ ≤ stage S := by unfold stage constant; ring_nf; omega

def modulusMajorant (S : ℕ) : ℕ :=
  S * (50 * (S + 1) * (2 + (S + 1) * S)) + S * (7 * S + 5) +
    2 * (S + 1) * (16 * S + 16) + 7 * (1 + S * S) + 7 * S + 18

theorem modulus_le (base exponent : List Bool) (S : ℕ)
    (hb : base.length ≤ S) (he : exponent.length ≤ S)
    (hv : BinaryArithmetic.toNat exponent ≤ S) :
    SubexpModulusMachine.runtimeBound base exponent ≤ modulusMajorant S := by
  rw [SubexpModulusMachine.runtimeBound_eq]
  unfold modulusMajorant
  gcongr

def localMajorant (S : ℕ) : ℕ :=
  9 * S + modulusMajorant S + 54 * S + 101 + 1400 * (10 * S + 4 + 1) +
    (39 * S + 55) + 2100 * (S + S + 2)^2 + 25000 * (S + 1)^2 +
    600 * (10 * S + 4 + 1) + 25 * (2 * (10 * S + 4) + 3) + 1

theorem storage_le (p μ S : ℕ) (prime precision : List Bool)
    (hb : baseWidth p 1 ≤ S) (hB : baseWidth p μ ≤ S)
    (hp : prime.length ≤ S) (he : precision.length ≤ S) :
    SubexpPreparedQuarticSetup.storageBound p μ prime precision ≤ 10 * S + 4 := by
  unfold SubexpPreparedQuarticSetup.storageBound
  omega

theorem localBudget_le (p D S : ℕ) (prime precision : List Bool)
    (hb : baseWidth p 1 ≤ S) (hB : baseWidth p (D + 1) ≤ S)
    (hp : prime.length ≤ S) (he : precision.length ≤ S)
    (hv : BinaryArithmetic.toNat precision ≤ S) :
    SubexpPreparedRingStaging.localBudget p D prime precision ≤ localMajorant S := by
  have hstorage := storage_le p (D + 1) S prime precision hb hB hp he
  have hcanonical : (SubexpPreparedQuarticPrelude.primeWord p).length ≤ S := by
    simpa only [SubexpPreparedQuarticPrelude.primeWord_length, baseWidth, one_mul] using hb
  have hm := modulus_le (SubexpPreparedQuarticPrelude.primeWord p) precision S hcanonical he hv
  unfold SubexpPreparedRingStaging.localBudget SubexpPreparedQuarticSetup.runtimeBound
    SubexpPreparedQuarticSetup.arithmeticBound SubexpPreparedQuarticPrelude.runtimeBound
    localMajorant
  gcongr

theorem rings_le (p D S bits : ℕ) (prime precision : List Bool)
    (hb : baseWidth p 1 ≤ S) (hB : baseWidth p (D + 1) ≤ S)
    (hp : prime.length ≤ S) (he : precision.length ≤ S)
    (hv : BinaryArithmetic.toNat precision ≤ S) (hS : 1 ≤ S) (hbits : bits ≤ 51 * S) :
    SubexpPreparedRingStaging.runtimeBound p D
      (bits + SubexpPreparedQuarticSetup.storageBound p (D + 1) prime precision +
        SubexpPreparedQuarticSetup.storageBound p 1 prime [true] + 1)
      prime precision ≤ stage S := by
  have hlocal := localBudget_le p D S prime precision hb hB hp he hv
  have hsource := localBudget_le p 0 S prime [true] hb hb hp (by simpa using hS) (by simpa using hS)
  have hstorage := storage_le p (D + 1) S prime precision hb hB hp he
  have hstorage' := storage_le p 1 S prime [true] hb hb hp (by simpa using hS)
  unfold SubexpPreparedRingStaging.runtimeBound
  calc
    _ ≤ localMajorant S + localMajorant S + 1000 * (71 * S + 10) := by omega
    _ ≤ stage S := by unfold stage constant localMajorant modulusMajorant; ring_nf; omega

theorem nodes_le (p μ S bits : ℕ) (hp : p ≤ S) (hq : p^4 ≤ S)
    (hb : baseWidth p 1 ≤ S) (hB : baseWidth p μ ≤ S) (hbits : bits ≤ 25 * S) :
    SubexpFieldNodeStaging.runtimeBound p μ bits ≤ stage S := by
  have hq' : p^4 - 1 + 1 ≤ S + 1 := by omega
  unfold SubexpFieldNodeStaging.runtimeBound SubexpFieldNodeStaging.generatorBudget
    SubexpFieldNodeStaging.mapperBudget
  calc
    _ ≤ 300 * (25 * S + 1200 * (S + 1)^4 * (25 * S + 1) +
        2500 * (S + 1) * (S + S + 2)^2 + 1) := by gcongr
    _ ≤ stage S := by unfold stage constant; ring_nf; omega

theorem field_le (S : ℕ) :
    SubexpFieldCacheProgram.polynomialBound S + 15 * S + 32 ≤ stage S := by
  unfold SubexpFieldCacheProgram.polynomialBound SubexpFieldCacheProgram.nodeBound
    SubexpFieldCacheProgram.pairBound SubexpFieldCacheProgram.rowBound
    SubexpFieldCacheProgram.stepBound stage constant
  ring_nf
  omega

theorem lagrange_le (S : ℕ) :
    248 * (2 * S + 3) + 100000000 * (1 + 11 * S)^8 + 758 ≤ stage S := by
  unfold stage constant
  ring_nf
  omega

theorem grow_add_one_le (S : ℕ) : grow S + 1 ≤ (constant + 3) * (S + 1)^8 := by
  have hpower : S + 1 ≤ (S + 1)^8 := by
    exact Nat.le_self_pow (by decide) _
  unfold grow stage
  rw [Nat.add_mul]
  omega

def coefficient : ℕ → ℕ
  | 0 => 1
  | n + 1 => (constant + 3) * coefficient n ^ 8

theorem iterate_bound (n S : ℕ) :
    iterate n S + 1 ≤ coefficient n * (S + 1)^(8^n) := by
  induction n with
  | zero => simp [iterate, coefficient]
  | succ n ih =>
    calc
      iterate (n + 1) S + 1 ≤ (constant + 3) * (iterate n S + 1)^8 :=
        grow_add_one_le _
      _ ≤ (constant + 3) * (coefficient n * (S + 1)^(8^n))^8 := by gcongr
      _ = coefficient (n + 1) * (S + 1)^(8^(n + 1)) := by
        rw [mul_pow, ← pow_mul, pow_succ 8 n, coefficient]
        exact (Nat.mul_assoc _ _ _).symm

def polynomialConstant : ℕ := coefficient 5 * 2^(8^5)
def polynomialDegree : ℕ := 4 * 8^5

theorem power_scale (C d q : ℕ) (hq : 1 ≤ q) :
    C * (q^4 + 1)^d ≤ (C * 2^d) * q^(4*d) := by
  have hpow : 1 ≤ q^4 := Nat.one_le_pow _ _ hq
  calc
    C * (q^4 + 1)^d ≤ C * (2 * q^4)^d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega : q^4 + 1 ≤ 2 * q^4) d)
    _ = (C * 2^d) * q^(4*d) := by
      rw [mul_pow, ← pow_mul]
      exact (Nat.mul_assoc _ _ _).symm

theorem iterate_five_le (q : ℕ) (hq : 1 ≤ q) :
    iterate 5 (q^4) ≤ polynomialConstant * q^polynomialDegree := by
  have hb := iterate_bound 5 (q^4)
  exact ((Nat.le_succ _).trans hb).trans (power_scale (coefficient 5) (8^5) q hq)

end SubexponentialSAT.SubexpMainLayoutCacheArithmetic

end OAI.Algorithms
