import OAI.Analysis.PDE.Dirichlet.Linear.FluxTransport

open Set Filter InnerProductSpace
open scoped ContDiff Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem contDiff_linearPullbackCoefficient (L : E ≃L[ℝ] F)
    {A : F → F →L[ℝ] F} {k : ℕ∞ω} (hA : ContDiff ℝ k A) :
    ContDiff ℝ k (linearPullbackCoefficient L A) := by
  unfold linearPullbackCoefficient
  exact contDiff_const.clm_comp ((hA.comp L.contDiff).clm_comp contDiff_const)

/-- The coefficient bound changes by a fixed coordinate constant only. -/
theorem norm_linearPullbackCoefficient_le (L : E ≃L[ℝ] F)
    (A : F → F →L[ℝ] F) (x : E) :
    ‖linearPullbackCoefficient L A x‖ ≤
      ‖L.symm.toContinuousLinearMap‖ ^ 2 * ‖A (L x)‖ := by
  let T := L.symm.toContinuousLinearMap
  change ‖T.comp ((A (L x)).comp T.adjoint)‖ ≤ ‖T‖ ^ 2 * ‖A (L x)‖
  calc
    _ ≤ ‖T‖ * ‖(A (L x)).comp T.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖T‖ * (‖A (L x)‖ * ‖T.adjoint‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by rw [LinearIsometryEquiv.norm_map]; ring

theorem norm_sub_linearPullbackCoefficient_le (L : E ≃L[ℝ] F)
    (A : F → F →L[ℝ] F) (x y : E) :
    ‖linearPullbackCoefficient L A x - linearPullbackCoefficient L A y‖ ≤
      ‖L.symm.toContinuousLinearMap‖ ^ 2 * ‖A (L x) - A (L y)‖ := by
  have he : linearPullbackCoefficient L A x - linearPullbackCoefficient L A y =
      linearPullbackCoefficient L (fun z ↦ A z - A (L y)) x := by
    simp only [linearPullbackCoefficient, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_sub]
  rw [he]
  exact norm_linearPullbackCoefficient_le L _ x

/-- Ellipticity is preserved under the same nonorthogonal coordinate
change used for the actual PDE. The denominator is positive even for a
trivial space, so no hidden nontriviality premise is needed. -/
theorem linearPullbackCoefficient_elliptic (L : E ≃L[ℝ] F)
    (A : F → F →L[ℝ] F) {x : E} {lam : ℝ} (hlam : 0 ≤ lam)
    (hell : ∀ z, lam * ‖z‖ ^ 2 ≤ inner ℝ (A (L x) z) z) (v : E) :
    (lam / (‖L.toContinuousLinearMap‖ + 1) ^ 2) * ‖v‖ ^ 2 ≤
      inner ℝ (linearPullbackCoefficient L A x v) v := by
  let w := L.symm.toContinuousLinearMap.adjoint v
  let B := ‖L.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hrec : L.toContinuousLinearMap.adjoint w = v := by
    simpa only [w, ContinuousLinearEquiv.symm_symm] using inverse_adjoint_cancel L.symm v
  have hv : ‖v‖ ≤ ‖L.toContinuousLinearMap‖ * ‖w‖ := by
    calc
      ‖v‖ = ‖L.toContinuousLinearMap.adjoint w‖ := congrArg norm hrec.symm
      _ ≤ ‖L.toContinuousLinearMap.adjoint‖ * ‖w‖ :=
        L.toContinuousLinearMap.adjoint.le_opNorm w
      _ = _ := by rw [LinearIsometryEquiv.norm_map]
  have hvB : ‖v‖ ≤ B * ‖w‖ := hv.trans
    (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (norm_nonneg w))
  have hsq : ‖v‖ ^ 2 ≤ B ^ 2 * ‖w‖ ^ 2 := by
    calc
      ‖v‖ ^ 2 ≤ (B * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvB 2
      _ = _ := mul_pow B ‖w‖ 2
  rw [linearPullbackCoefficient_quadratic]
  change (lam / B ^ 2) * ‖v‖ ^ 2 ≤ inner ℝ (A (L x) w) w
  calc
    _ ≤ (lam / B ^ 2) * (B ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (div_nonneg hlam (sq_nonneg _))
    _ = lam * ‖w‖ ^ 2 := by field_simp
    _ ≤ _ := hell w

end OAI.Analysis.PDE.Dirichlet
