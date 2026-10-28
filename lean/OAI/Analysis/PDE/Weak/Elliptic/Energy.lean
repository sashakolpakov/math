import OAI.Analysis.PDE.Weak.Elliptic.Difference

/-! The concrete cutoff energy and the coefficient commutator. -/

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem differenceQuotient_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : X) (h : ℝ) (A : X → E →L[ℝ] E) (G : X → E) (x : X) :
    differenceQuotient v h (fun y ↦ A y (G y)) x =
      A (x + h • v) (differenceQuotient v h G x) +
        (differenceQuotient v h A x) (G x) := by
  simp only [differenceQuotient, map_smul, map_sub, smul_apply,
    sub_apply]
  module

theorem weightedYoung {lam : ℝ} (hlam : 0 < lam) (a b : ℝ) :
    2 * a * b ≤ lam * a ^ 2 + lam⁻¹ * b ^ 2 := by
  apply (mul_le_mul_iff_right₀ hlam).mp
  have hi : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
  nlinarith [sq_nonneg (lam * a - b)]

theorem cutoff_energy_pointwise (A : E →L[ℝ] E) {lam Λ : ℝ}
    (hlam : 0 < lam) (_ : 0 ≤ Λ) (hA : ‖A‖ ≤ Λ)
    (hell : ∀ p : E, lam * ‖p‖ ^ 2 ≤ inner ℝ (A p) p)
    (η u : ℝ) (p g : E) :
    (lam / 2) * η ^ 2 * ‖p‖ ^ 2 ≤
      inner ℝ (A p) (η ^ 2 • p + (2 * η * u) • g) +
        (2 * Λ ^ 2 / lam) * u ^ 2 * ‖g‖ ^ 2 := by
  have hinner : |inner ℝ (A p) g| ≤ Λ * ‖p‖ * ‖g‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        ((A.le_opNorm p).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
        (norm_nonneg _))
  have hcross : -(2 * |η| * |u| * (Λ * ‖p‖ * ‖g‖)) ≤
      2 * η * u * inner ℝ (A p) g := by
    have hab := neg_abs_le (2 * η * u * inner ℝ (A p) g)
    have hm := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 2 * |η| * |u| by positivity)
    norm_num only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hab
    linarith
  have hprincipal := mul_le_mul_of_nonneg_left (hell p) (sq_nonneg η)
  have hy := weightedYoung (show 0 < lam / 2 by positivity)
    (|η| * ‖p‖) (Λ * |u| * ‖g‖)
  have hη : |η| ^ 2 = η ^ 2 := sq_abs η
  have hu : |u| ^ 2 = u ^ 2 := sq_abs u
  have hinv : (lam / 2)⁻¹ = 2 / lam := by field_simp
  rw [hinv] at hy
  simp only [mul_pow, hη, hu] at hy
  simp only [inner_add_right, real_inner_smul_right]
  simp only [div_eq_mul_inv] at hy ⊢
  nlinarith

variable [CompleteSpace E]

theorem gradient_cutoff_square {η u : E → ℝ}
    (hη : Differentiable ℝ η) (hu : Differentiable ℝ u) (x : E) :
    gradient (fun y ↦ η y ^ 2 * u y) x =
      η x ^ 2 • gradient u x + (2 * η x * u x) • gradient η x := by
  apply (toDual ℝ E).injective
  rw [toDual_gradient, map_add, map_smul, map_smul,
    toDual_gradient, toDual_gradient]
  change fderiv ℝ ((fun y ↦ η y ^ 2) * u) x = _
  rw [(((hη x).hasFDerivAt.pow 2).mul (hu x).hasFDerivAt).fderiv]
  ext v
  simp
  ring

theorem gradient_differenceQuotient (v : E) (h : ℝ) {u : E → ℝ}
    (hu : Differentiable ℝ u) (x : E) :
    gradient (differenceQuotient v h u) x = differenceQuotient v h (gradient u) x := by
  apply (toDual ℝ E).injective
  rw [toDual_gradient]
  ext w
  rw [fderiv_differenceQuotient v h hu x w]
  simp [differenceQuotient, toDual_gradient]

end OAI.Analysis.PDE.Weak
