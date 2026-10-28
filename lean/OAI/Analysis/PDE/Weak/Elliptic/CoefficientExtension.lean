import OAI.Analysis.PDE.Weak.Elliptic.InteriorH2

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A local elliptic field is joined to a constant elliptic field outside
the support of a cutoff.  Convexity preserves the same ellipticity constant. -/
def ellipticExtension (A : X → E →L[ℝ] E) (θ : X → ℝ) (lam : ℝ) (x : X) : E →L[ℝ] E :=
  θ x • A x + (1 - θ x) • (lam • ContinuousLinearMap.id ℝ E)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem ellipticExtension_eq {A : X → E →L[ℝ] E} {θ : X → ℝ}
    (lam : ℝ) {x : X} (hx : θ x = 1) : ellipticExtension A θ lam x = A x := by
  simp [ellipticExtension, hx]

theorem contDiff_ellipticExtension {A : X → E →L[ℝ] E} {θ : X → ℝ}
    (hA : ContDiff ℝ 1 A) (hθ : ContDiff ℝ 1 θ) (lam : ℝ) :
    ContDiff ℝ 1 (ellipticExtension A θ lam) :=
  (hθ.smul hA).add ((contDiff_const.sub hθ).smul contDiff_const)

omit [NormedSpace ℝ X] in
theorem ellipticExtension_elliptic {A : X → E →L[ℝ] E} {θ : X → ℝ}
    {Ω : Set X} {lam : ℝ} (hθ : ∀ x, θ x ∈ Icc (0 : ℝ) 1)
    (hs : tsupport θ ⊆ Ω)
    (hell : ∀ x ∈ Ω, ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A x z) z) :
    ∀ x z, lam * ‖z‖ ^ 2 ≤ inner ℝ (ellipticExtension A θ lam x z) z := by
  intro x z
  by_cases hx : θ x = 0
  · simp [ellipticExtension, hx, real_inner_smul_left]
  · have hAx := hell x (hs (subset_tsupport θ hx)) z
    have hm := mul_le_mul_of_nonneg_left hAx (hθ x).1
    simp only [ellipticExtension, add_apply,
      smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith

theorem ellipticExtension_bounded_C1 [CompleteSpace E] {A : X → E →L[ℝ] E} {θ : X → ℝ}
    (hA : ContDiff ℝ 1 A) (hθ : ContDiff ℝ 1 θ) (hs : HasCompactSupport θ) (lam : ℝ) :
    ∃ M D : ℝ, 0 ≤ M ∧ 0 ≤ D ∧
      (∀ x, ‖ellipticExtension A θ lam x‖ ≤ M) ∧
      (∀ x, ‖fderiv ℝ (ellipticExtension A θ lam) x‖ ≤ D) := by
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (X →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let C : E →L[ℝ] E := lam • ContinuousLinearMap.id ℝ E
  let B : X → E →L[ℝ] E := fun x ↦ θ x • (A x - C)
  have hB : ContDiff ℝ 1 B := hθ.smul (hA.sub contDiff_const)
  have hBs : HasCompactSupport B := hs.smul_right
  obtain ⟨M, hM⟩ := (hBs.isCompact_range hB.continuous).isBounded.exists_norm_le
  have hDBs : HasCompactSupport (fderiv ℝ B) := hBs.fderiv (𝕜 := ℝ)
  have hDBc : Continuous (fderiv ℝ B) := hB.continuous_fderiv one_ne_zero
  have hDBnorm : Continuous (fun x ↦ ‖fderiv ℝ B x‖) := hDBc.norm
  obtain ⟨D, hD⟩ := (hDBs.norm.isCompact_range hDBnorm).bddAbove
  have hM0 : 0 ≤ M := (norm_nonneg (B 0)).trans (hM _ (mem_range_self 0))
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ B 0)).trans (hD (mem_range_self 0))
  have he : ellipticExtension A θ lam = fun x ↦ C + B x := by
    funext x
    dsimp [ellipticExtension, C, B]
    module
  refine ⟨‖C‖ + M, D, by positivity, hD0, ?_, ?_⟩
  · intro x
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hM _ (mem_range_self x)))
  · intro x
    rw [he]
    have hd := (((hB.differentiable one_ne_zero) x).hasFDerivAt.const_add C).fderiv
    rw [hd]
    exact hD (mem_range_self x)

end OAI.Analysis.PDE.Weak
