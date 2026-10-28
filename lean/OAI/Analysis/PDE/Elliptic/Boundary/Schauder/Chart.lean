import OAI.Analysis.PDE.Elliptic.Boundary.Schauder.Coefficient

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The coefficient bound for a fixed smooth chart is chosen before the
coefficient field. In particular it requires only its Hölder norm, not
derivatives or smoothness of the field. -/
theorem exists_chart_coefficient_holder_constant
    (G P : E → E) (hG : ContDiff ℝ 2 G) (hP : ContDiff ℝ 2 P)
    {S : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : E → E →L[ℝ] E) (N : ℝ), 0 ≤ N →
      (∀ x ∈ S, ‖A (G x)‖ ≤ N) →
      (∀ x ∈ S, ∀ y ∈ S, ‖A (G x)-A (G y)‖ ≤ N * ‖G x-G y‖^α) →
      (∀ x ∈ S, ‖pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))‖ ≤ C*N) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        ‖pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x)) -
          pullbackEllipticOperator (fderiv ℝ P (G y)) (A (G y))‖ ≤ C*N*‖x-y‖^α) := by
  let J := fun x => fderiv ℝ P (G x)
  have hJ : ContDiff ℝ 1 J := (hP.fderiv_right (by norm_num)).comp (hG.of_le (by norm_num))
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn hJ.continuous.continuousOn
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn
    (hJ.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨M₂, hM₂⟩ := hS.exists_bound_of_continuousOn
    (hG.continuous_fderiv (by norm_num)).continuousOn
  let L := max 1 (max M₀ (max M₁ M₂))
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h₀ : M₀ ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  have h₁ : M₁ ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₂ : M₂ ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hJn : ∀ x ∈ S, ‖J x‖ ≤ L := fun x hx => (hM₀ x hx).trans h₀
  have hJh : ∀ x ∈ S, ∀ y ∈ S, ‖J x-J y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hJ.differentiable one_ne_zero z) (fun z hz => (hM₁ z hz).trans h₁) hSc hy hx
  have hGh : ∀ x ∈ S, ∀ y ∈ S, ‖G x-G y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hG.differentiable (by norm_num) z) (fun z hz => (hM₂ z hz).trans h₂) hSc hy hx
  let C := L^2 + (L^2 * L^α + 2*L^2) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hnorm : L^2 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (sq_nonneg L) (Real.rpow_nonneg hL.le α), sq_nonneg L]
  have hhold : L^2 * L^α + 2*L^2 ≤ C := by dsimp [C]; nlinarith [sq_nonneg L]
  refine ⟨C, hC, ?_⟩
  intro A N hN hAn hAh
  obtain ⟨hn, hh⟩ := pullback_coefficient_holder_on_unit_diameter A G J hL.le hN hα hα1
    hdiam hAn hAh hJn hJh hGh
  constructor
  · intro x hx
    exact (hn x hx).trans (mul_le_mul_of_nonneg_right hnorm hN)
  · intro x hx y hy
    exact (hh x hx y hy).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hhold hN) (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Elliptic
