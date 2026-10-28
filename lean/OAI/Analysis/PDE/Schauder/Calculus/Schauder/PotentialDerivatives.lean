import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Potential

/-! Differentiation of the Newtonian convolution on the compact smooth data. -/

noncomputable section
open _root_.MeasureTheory
open scoped Convolution
namespace OAI.Analysis.PDE.Schauder

theorem fderiv_newtonianPotential_apply {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x v : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (newtonianPotential f) x v = newtonianPotential (fun y => fderiv ℝ f y v) x := by
  have hi := (hfc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m)))
    (locallyIntegrable_newtonianKernel hm) (hf.continuous_fderiv one_ne_zero) x
  rw [(hasFDerivAt_newtonianPotential hm f hf hfc x).fderiv]
  change (∫ y, (ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m))
    (newtonianKernel m y) (fderiv ℝ f (x - y))) v = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem fderiv_apply_const {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → E →L[ℝ] F) (x v w : E) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun y => g y v) x w = fderiv ℝ g x w v := by
  rw [fderiv_clm_apply hg (differentiableAt_const v)]
  simp

theorem second_fderiv_newtonianPotential_apply {m : ℕ} (hm : 1 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (x v w : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fderiv ℝ (newtonianPotential f)) x v w =
      newtonianPotential (fun y => fderiv ℝ (fderiv ℝ f) y v w) x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 1 (fun y => fderiv ℝ f y w) := hDf.clm_apply contDiff_const
  have hU : ContDiff ℝ 2 (newtonianPotential f) := contDiff_newtonianPotential hm f hf hfc
  have hDU : ContDiff ℝ 1 (fderiv ℝ (newtonianPotential f)) := hU.fderiv_right (by norm_num)
  have he : (fun y => fderiv ℝ (newtonianPotential f) y w) =
      newtonianPotential (fun y => fderiv ℝ f y w) :=
    funext (fun y => fderiv_newtonianPotential_apply hm f hf1 hfc y w)
  rw [← fderiv_apply_const _ x w v (hDU.differentiable one_ne_zero x), he,
    fderiv_newtonianPotential_apply hm _ hg (hfc.fderiv_apply ℝ w)]
  congr 1
  funext y
  exact fderiv_apply_const _ y w v (hDf.differentiable one_ne_zero y)

end OAI.Analysis.PDE.Schauder
