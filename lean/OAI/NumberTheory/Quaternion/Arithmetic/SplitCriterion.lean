import OAI.NumberTheory.Quaternion.Arithmetic.MatrixGroup

/-! # Split Criterion -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SplitCriterion

noncomputable section

/-! A nonzero quaternion of zero reduced norm gives a splitting
norm equation. Thus a quaternion algebra without a ground-field
splitting solution has anisotropic reduced norm. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra

variable {K : Type} [Field K] [CharZero K]

theorem binary_norm_of_square_coefficient (a b z : K) (ha : a ≠ 0) (hz : z ^ 2 = a) :
    ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
  have hz0 : z ≠ 0 := by
    intro h
    apply ha
    simpa only [h, zero_pow (by decide : 2 ≠ 0)] using hz.symm
  refine ⟨(b + 1) / 2, (b - 1) / (2 * z), ?_⟩
  rw [← hz]
  field_simp
  ring

omit [CharZero K] in
theorem binary_norm_quotient (a r s t u : K) (hδ : t ^ 2 - a * u ^ 2 ≠ 0) :
    ((r * t - a * s * u) / (t ^ 2 - a * u ^ 2)) ^ 2 -
      a * ((s * t - r * u) / (t ^ 2 - a * u ^ 2)) ^ 2 =
        (r ^ 2 - a * s ^ 2) / (t ^ 2 - a * u ^ 2) := by
  field_simp
  ring

theorem quaternion_zero_norm_implies_splitting_equation (a b : K) (ha : a ≠ 0)
    (q : ℍ[K,a,b]) (hq : q ≠ 0) (hn : Norm.quaternionNorm a b q = 0) :
    ∃ x y : K, x ^ 2 - a * y ^ 2 = b := by
  have he : q.re ^ 2 - a * q.imI ^ 2 = b * (q.imJ ^ 2 - a * q.imK ^ 2) := by
    rw [Norm.quaternionNorm_formula] at hn
    linear_combination hn
  by_cases hδ : q.imJ ^ 2 - a * q.imK ^ 2 = 0
  · have hnum : q.re ^ 2 - a * q.imI ^ 2 = 0 := by rw [he, hδ, mul_zero]
    by_cases hi : q.imI = 0
    · by_cases hk : q.imK = 0
      · have hr : q.re = 0 := by
          have hsq : q.re ^ 2 = 0 := by simpa only [hi, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using hnum
          exact (sq_eq_zero_iff).mp hsq
        have hj : q.imJ = 0 := by
          have hsq : q.imJ ^ 2 = 0 := by simpa only [hk, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using hδ
          exact (sq_eq_zero_iff).mp hsq
        exact (hq (QuaternionAlgebra.ext hr hi hj hk)).elim
      · apply binary_norm_of_square_coefficient a b (q.imJ / q.imK) ha
        apply (div_pow q.imJ q.imK 2).trans
        apply (div_eq_iff (pow_ne_zero _ hk)).mpr
        exact sub_eq_zero.mp hδ
    · apply binary_norm_of_square_coefficient a b (q.re / q.imI) ha
      apply (div_pow q.re q.imI 2).trans
      apply (div_eq_iff (pow_ne_zero _ hi)).mpr
      exact sub_eq_zero.mp hnum
  · refine ⟨(q.re * q.imJ - a * q.imI * q.imK) / (q.imJ ^ 2 - a * q.imK ^ 2),
      (q.imI * q.imJ - q.re * q.imK) / (q.imJ ^ 2 - a * q.imK ^ 2), ?_⟩
    rw [binary_norm_quotient a q.re q.imI q.imJ q.imK hδ]
    exact (div_eq_iff hδ).mpr he

theorem quaternion_norm_anisotropic_of_no_splitting_equation (a b : K) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : K, x ^ 2 - a * y ^ 2 = b)
    (q : ℍ[K,a,b]) (hn : Norm.quaternionNorm a b q = 0) : q = 0 := by
  by_contra hq
  exact hs (quaternion_zero_norm_implies_splitting_equation a b ha q hq hn)

end

end OAI.NumberTheory.Quaternion.Arithmetic.SplitCriterion
