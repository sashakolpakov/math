import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyKernel

/-! # Vector Cauchy Transform -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyTransform.Dolbeault

noncomputable section

/-! The genuine Cauchy integral with values in a complex Banach space.
This supplies a common operator for all coefficients of differential forms. -/

open _root_.MeasureTheory _root_.ContinuousLinearMap
open scoped Convolution ContDiff

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G]

def vectorCauchyTransform (f : ℂ → F) : ℂ → F :=
  DivisorClass.Chern.CauchyKernel.cauchyKernel ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] f

theorem vectorCauchyTransform_apply (f : ℂ → F) (z : ℂ) :
    vectorCauchyTransform f z = ∫ w : ℂ, DivisorClass.Chern.CauchyKernel.cauchyKernel w • f (z - w) := rfl

theorem vectorCauchyTransform_smooth {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (vectorCauchyTransform f) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ) DivisorClass.Chern.CauchyKernel.cauchyKernel_locallyIntegrable hf

theorem vectorCauchyTransform_hasFDerivAt {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (z : ℂ) :
    HasFDerivAt (vectorCauchyTransform f)
      ((DivisorClass.Chern.CauchyKernel.cauchyKernel ⋆[(ContinuousLinearMap.lsmul ℝ ℂ).precompR ℂ, volume]
        fderiv ℝ f) z) z :=
  hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    DivisorClass.Chern.CauchyKernel.cauchyKernel_locallyIntegrable hf z

theorem vectorCauchyTransform_map [CompleteSpace F] [CompleteSpace G]
    (L : F →L[ℂ] G) {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : Continuous f) (z : ℂ) :
    L (vectorCauchyTransform f z) = vectorCauchyTransform (L ∘ f) z := by
  have hi := hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℂ)
    DivisorClass.Chern.CauchyKernel.cauchyKernel_locallyIntegrable hf z
  have hI : Integrable (fun w : ℂ => DivisorClass.Chern.CauchyKernel.cauchyKernel w • f (z - w)) := hi.integrable
  change (L.restrictScalars ℝ) (∫ w : ℂ, DivisorClass.Chern.CauchyKernel.cauchyKernel w • f (z - w)) =
    ∫ w : ℂ, DivisorClass.Chern.CauchyKernel.cauchyKernel w • L (f (z - w))
  rw [← (L.restrictScalars ℝ).integral_comp_comm hI]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => L.map_smul (DivisorClass.Chern.CauchyKernel.cauchyKernel w) (f (z - w)))

theorem vectorCauchyTransform_scalar (f : ℂ → ℂ) :
    vectorCauchyTransform f = DivisorClass.Chern.CauchyKernel.cauchyTransform f := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.VectorCauchyTransform.Dolbeault
