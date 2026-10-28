import OAI.Analysis.PDE.Elliptic.Boundary.Holder

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem ellipticTrace_slope_rescale_center (A : E → E →L[ℝ] E) {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (z : E) {R : ℝ} (hR : R ≠ 0) (x : E) :
    ellipticTrace (fun y => A (z + R • y)) (fun y => R⁻¹ * u (z + R • y)) x =
      R * ellipticTrace A u (z + R • x) := by
  have hh : ContDiff ℝ 2 (fun y : E => u (z + R • y)) :=
    hu.comp (contDiff_const.add (contDiff_id.const_smul R))
  have hs := ellipticTrace_smul (fun y => A (z + R • y)) hh R⁻¹ x
  simp only [smul_eq_mul] at hs
  rw [hs]
  have he := ellipticTrace_rescalePoint A hu z R x
  change ellipticTrace (fun y => A (z + R • y)) (fun y => u (z + R • y)) x = _ at he
  rw [he]
  change R⁻¹ * (R ^ 2 * ellipticTrace A u (z + R • x)) = _
  field_simp

omit [FiniteDimensional ℝ E] in
theorem fderiv_slope_rescale_center {u : E → ℝ}
    (hu : ContDiff ℝ 2 u) (z : E) {R : ℝ} (hR : R ≠ 0) (x w : E) :
    fderiv ℝ (fun y => R⁻¹ * u (z + R • y)) x w = fderiv ℝ u (z + R • x) w := by
  have hd := (((hu.differentiable (by norm_num) (z + R • x)).hasFDerivAt.comp x
    (hasFDerivAt_rescalePoint z R x)).const_smul R⁻¹).fderiv
  change fderiv ℝ (fun y => R⁻¹ * u (z + R • y)) x = _ at hd
  rw [hd]
  simp [smul_smul, hR]

end OAI.Analysis.PDE.Elliptic
