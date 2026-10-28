import OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates

/-! # Logarithm -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.Logarithm

noncomputable section

/-!
# Additivity of the actual crystalline logarithm

Raising units to p-power exponents makes their differences from one arbitrarily
p-divisible in the integral envelope. The proved power identity and first-order
estimates then give the product identity by cancellation in adic quotients.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Cyclotomic OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates

theorem mapped_mul_difference_eq_zero {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* T) (q : S →+* T) (c a b d : R) (a' b' d' : S)
    (ha : f (c * a) = q a') (hb : f (c * b) = q b') (hd : f (c * d) = q d')
    (h : q (a' - (b' + d')) = 0) : f (c * (a - (b + d))) = 0 := by
  rw [mul_sub, mul_add, map_sub, map_add, ha, hb, hd, ← map_add, ← map_sub, h]

variable (p : ℕ) [Fact p.Prime]

def productKernelElement (x y : RingHom.ker (PeriodRing.theta p)) : RingHom.ker (PeriodRing.theta p) :=
  ⟨(x : PeriodRing.Ainf p) + y + x * y, by
    rw [RingHom.mem_ker, map_add, map_add, map_mul,
      RingHom.mem_ker.mp x.property, RingHom.mem_ker.mp y.property]
    simp⟩

theorem one_add_productKernelElement (x y : RingHom.ker (PeriodRing.theta p)) :
    (1 + (productKernelElement p x y : PeriodRing.Ainf p)) = (1 + (x : PeriodRing.Ainf p)) * (1 + y) := by
  change 1 + ((x : PeriodRing.Ainf p) + y + x * y) = _
  ring

theorem power_productKernelElement (x y : RingHom.ker (PeriodRing.theta p)) (N : ℕ) :
    Cyclotomic.powerKernelElement p (productKernelElement p x y) N =
      productKernelElement p (Cyclotomic.powerKernelElement p x N) (Cyclotomic.powerKernelElement p y N) := by
  apply Subtype.val_injective
  change (1 + (productKernelElement p x y : PeriodRing.Ainf p)) ^ N - 1 =
    ((1 + (x : PeriodRing.Ainf p)) ^ N - 1) + ((1 + (y : PeriodRing.Ainf p)) ^ N - 1) +
      ((1 + (x : PeriodRing.Ainf p)) ^ N - 1) * ((1 + (y : PeriodRing.Ainf p)) ^ N - 1)
  rw [one_add_productKernelElement, mul_pow]
  ring

theorem pdLog_power_linear_eval (x : RingHom.ker (PeriodRing.theta p)) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) ((n + 2) + n)
        ((p : PeriodRing.Acris p) ^ (n + 2) * PeriodRing.pdLog p x) =
      Ideal.Quotient.mk ((Ideal.span {(p : PeriodRing.AcrisZero p)}) ^ ((n + 2) + n))
        (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p)
          (Cyclotomic.powerKernelElement p x (p ^ (n + 2)))) := by
  have hpower : (p : PeriodRing.Acris p) ^ (n + 2) * PeriodRing.pdLog p x =
      PeriodRing.pdLog p (Cyclotomic.powerKernelElement p x (p ^ (n + 2))) := by
    simpa only [Nat.cast_pow] using (Cyclotomic.pdLog_power p x (p ^ (n + 2))).symm
  rw [hpower]
  apply AdicEstimates.pdLog_firstOrder_eval p (Cyclotomic.powerKernelElement p x (p ^ (n + 2))) (n + 1)
    ((n + 2) + n) (by omega)
  change (p : PeriodRing.AcrisZero p) ^ (n + 2) ∣
    algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) ((1 + (x : PeriodRing.Ainf p)) ^ (p ^ (n + 2)) - 1)
  simpa only [Nat.cast_pow] using AdicEstimates.power_difference_dvd p x (p ^ (n + 2))

theorem power_differences_mul_mem (x y : RingHom.ker (PeriodRing.theta p)) (n : ℕ) :
    algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p x (p ^ (n + 2))) *
      algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p y (p ^ (n + 2))) ∈
        (Ideal.span {(p : PeriodRing.AcrisZero p)}) ^ ((n + 2) + n) := by
  have hm := Ideal.mul_mem_mul (AdicEstimates.power_difference_mem_pow p x (n + 2))
    (AdicEstimates.power_difference_mem_pow p y (n + 2))
  rw [← pow_add] at hm
  exact Ideal.pow_le_pow_right (show (n + 2) + n ≤ (n + 2) + (n + 2) by omega) hm

theorem power_product_difference (x y : RingHom.ker (PeriodRing.theta p)) (N : ℕ) :
    algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p (productKernelElement p x y) N) -
      (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p x N) +
        algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p y N)) =
    algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p x N) *
      algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p y N) := by
  rw [power_productKernelElement]
  change algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p)
      ((Cyclotomic.powerKernelElement p x N : PeriodRing.Ainf p) + Cyclotomic.powerKernelElement p y N +
        (Cyclotomic.powerKernelElement p x N : PeriodRing.Ainf p) * Cyclotomic.powerKernelElement p y N) - _ = _
  rw [map_add, map_add, map_mul]
  ring

/-- The convergent divided-power logarithm sends products of units in
`1 + ker theta` to sums in the actual completed envelope. -/
theorem pdLog_product (x y : RingHom.ker (PeriodRing.theta p)) :
    PeriodRing.pdLog p (productKernelElement p x y) = PeriodRing.pdLog p x + PeriodRing.pdLog p y := by
  apply sub_eq_zero.mp
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [map_zero]
  apply AdicEstimates.completion_eval_pow_cancel p
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (n + 2) n
  apply mapped_mul_difference_eq_zero
    (AdicCompletion.evalₐ (Ideal.span {(p : PeriodRing.AcrisZero p)}) ((n + 2) + n)).toRingHom
    (Ideal.Quotient.mk ((Ideal.span {(p : PeriodRing.AcrisZero p)}) ^ ((n + 2) + n)))
    ((p : PeriodRing.Acris p) ^ (n + 2))
    (PeriodRing.pdLog p (productKernelElement p x y)) (PeriodRing.pdLog p x) (PeriodRing.pdLog p y)
    (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p)
      (Cyclotomic.powerKernelElement p (productKernelElement p x y) (p ^ (n + 2))))
    (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p x (p ^ (n + 2))))
    (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) (Cyclotomic.powerKernelElement p y (p ^ (n + 2))))
    (pdLog_power_linear_eval p (productKernelElement p x y) n)
    (pdLog_power_linear_eval p x n) (pdLog_power_linear_eval p y n)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [power_product_difference]
  exact power_differences_mul_mem p x y n

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.Logarithm
