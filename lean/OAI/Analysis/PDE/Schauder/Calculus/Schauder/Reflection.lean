import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Green

/-! Translation and reflection identities for actual Fréchet derivatives. -/

noncomputable section
namespace OAI.Analysis.PDE.Schauder

theorem fderiv_reflect_translate {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (hf : Differentiable ℝ f) (x y : E) :
    fderiv ℝ (fun z => f (x - z)) y = -fderiv ℝ f (x - y) := by
  have hg : HasFDerivAt (fun z : E => x - z) (-ContinuousLinearMap.id ℝ E) y := by
    simpa using! (hasFDerivAt_const x y).sub (hasFDerivAt_id y)
  simpa using! ((hf (x - y)).hasFDerivAt.comp y hg).fderiv

theorem second_fderiv_reflect_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (x y v w : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (x - z))) y v w =
      fderiv ℝ (fderiv ℝ f) (x - y) v w := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have he : fderiv ℝ (fun z => f (x - z)) = fun z => -fderiv ℝ f (x - z) := by
    funext z
    exact fderiv_reflect_translate f (hf.differentiable (by norm_num)) x z
  rw [he]
  change (fderiv ℝ (-(fun z => fderiv ℝ f (x - z))) y) v w = _
  rw [fderiv_neg, fderiv_reflect_translate (fderiv ℝ f) (hDf.differentiable one_ne_zero) x y, neg_neg]

end OAI.Analysis.PDE.Schauder
