import OAI.RepresentationTheory.Weil.UnitarySplitting.PartialSchwartzFourier

/-! # Coordinate Partial Fourier -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinatePartialFourier.Construction

noncomputable section

/-! Partial Fourier transform in the concrete finite coordinate model. -/

open _root_.MeasureTheory
open scoped SchwartzMap

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}

def positionEuclideanPairEquiv (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ) :
    (V × EuclideanSpace ℝ (Fin d)) ≃L[ℝ] (V × Local.FunctionsMetaplectic.Construction.Position ℝ d) :=
  (ContinuousLinearEquiv.refl ℝ V).prodCongr
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ))

def coordinatePartialFourier (f : SchwartzMap (V × Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ) :
    SchwartzMap (V × Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (positionEuclideanPairEquiv V d).symm
    (PartialSchwartzFourier.Construction.schwartzPartialFourier (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (positionEuclideanPairEquiv V d) f))

theorem coordinatePartialFourier_apply (f : SchwartzMap (V × Local.FunctionsMetaplectic.Construction.Position ℝ d) ℂ)
    (x : V × Local.FunctionsMetaplectic.Construction.Position ℝ d) :
    coordinatePartialFourier f x =
      ∫ y : Local.FunctionsMetaplectic.Construction.Position ℝ d, (Real.fourierChar (-(∑ i, y i * x.2 i)) : ℂ) * f (x.1, y) := by
  change PartialSchwartzFourier.Construction.partialFourierFunction (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (positionEuclideanPairEquiv V d) f) (x.1, WithLp.toLp 2 x.2) = _
  rw [PartialSchwartzFourier.Construction.partialFourierFunction_integral]
  rw [← (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 (Local.FunctionsMetaplectic.Construction.Position ℝ d)).measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change (Real.fourierChar (-inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x.2)) : ℂ) * f (x.1, y) = _
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    congr 3
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CoordinatePartialFourier.Construction
