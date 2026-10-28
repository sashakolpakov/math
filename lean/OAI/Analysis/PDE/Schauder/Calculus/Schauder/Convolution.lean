import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TruncationIntegral

/-! Differentiating a scalar convolution on either its compact data or its smooth kernel. -/

noncomputable section
open _root_.MeasureTheory
open scoped Convolution
namespace OAI.Analysis.PDE.Schauder

def scalarConvolution {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ℝ := ∫ y, K y * f (x - y)

theorem contDiff_scalarConvolution {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : LocallyIntegrable K) {k : ℕ∞} (hf : ContDiff ℝ k f) (hfc : HasCompactSupport f) :
    ContDiff ℝ k (scalarConvolution K f) :=
  hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hf

theorem fderiv_scalarConvolution_data {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : LocallyIntegrable K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (scalarConvolution K f) x u = ∫ y, K y * fderiv ℝ f (x - y) u := by
  have hi := (hfc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m)))
    hK (hf.continuous_fderiv one_ne_zero) x
  change fderiv ℝ (K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f) x u = _
  rw [(hfc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hf x).fderiv]
  change (∫ y, (ContinuousLinearMap.mul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin m))
    (K y) (fderiv ℝ f (x - y))) u = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem integral_convolution_fderiv_transfer {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 1 K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    (∫ y, K y * fderiv ℝ f (x - y) u) = ∫ y, fderiv ℝ K y u * f (x - y) := by
  have hg : ContDiff ℝ 1 (fun y => f (x - y)) := hf.comp (contDiff_const.sub contDiff_id)
  have hgc : HasCompactSupport (fun y => f (x - y)) := hfc.comp_homeomorph (Homeomorph.subLeft x)
  have h := integral_mul_fderiv_compact K (fun y => f (x - y)) hK hg hgc u
  simp only [fderiv_reflect_translate f (hf.differentiable one_ne_zero),
    neg_apply, mul_neg, integral_neg] at h
  linarith

theorem fderiv_scalarConvolution_kernel {m : ℕ} (K f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hK : ContDiff ℝ 1 K) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x u : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (scalarConvolution K f) x u = ∫ y, fderiv ℝ K y u * f (x - y) := by
  rw [fderiv_scalarConvolution_data K f hK.continuous.locallyIntegrable hf hfc x u,
    integral_convolution_fderiv_transfer K f hK hf hfc x u]

end OAI.Analysis.PDE.Schauder
