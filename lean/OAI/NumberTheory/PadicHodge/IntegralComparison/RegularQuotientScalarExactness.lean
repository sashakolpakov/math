import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Regular.SMul
import Mathlib.Algebra.Exact.Basic

/-! # Regular Quotient Scalar Exactness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RegularQuotientScalarExactness

noncomputable section

/-! Multiplication by a regular element and its complementary power is exact on the actual prime-power quotient. -/

universe u

variable (R : Type u) [CommRing R] (r : R) (hr : IsSMulRegular R r) (n : ℕ)

abbrev Ring := R ⧸ (Ideal.span {r}) ^ (n + 1)

def scalar : Ring R r n := Ideal.Quotient.mk ((Ideal.span {r}) ^ (n + 1)) r

theorem power_zero : scalar R r n ^ (n + 1) = 0 := by
  change (Ideal.Quotient.mk ((Ideal.span {r}) ^ (n + 1)) r) ^ (n + 1) = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton r)) (n + 1))

include hr in
theorem exact : Function.Exact
    (DistribSMul.toLinearMap (Ring R r n) (Ring R r n) (scalar R r n ^ n))
    (DistribSMul.toLinearMap (Ring R r n) (Ring R r n) (scalar R r n)) := by
  let q := Ideal.Quotient.mk ((Ideal.span {r}) ^ (n + 1))
  intro x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hm : r * a ∈ (Ideal.span {r}) ^ (n + 1) :=
      Ideal.Quotient.eq_zero_iff_mem.mp ((q.map_mul r a).trans hx)
    rw [Ideal.span_singleton_pow] at hm
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hm
    have he : a = r ^ n * b := hr (by
      change r * a = r * (r ^ n * b)
      exact hb.trans (by rw [pow_succ', mul_assoc]))
    refine ⟨q b, ?_⟩
    change q r ^ n * q b = q a
    exact ((q.map_pow r n).symm ▸ (q.map_mul (r ^ n) b).symm).trans (congrArg q he.symm)
  · rintro ⟨y, rfl⟩
    change scalar R r n * (scalar R r n ^ n * y) = 0
    rw [← mul_assoc, ← pow_succ', power_zero, zero_mul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RegularQuotientScalarExactness
