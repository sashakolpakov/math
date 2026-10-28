import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.MorphismCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineMorphismTensorCoordinates

/-! # Holomorphic Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Tensor transport is faithful on the actual holomorphic coefficient
families and agrees with the original algebraic tensor morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier} (H : HilbertConstruction.Line.Bundles.LineBundle V.carrier)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tripleFrame_ext {D E : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K}
    (he : ∀ (q : CommonLineFrames.TripleLineFrame L.sheaf K.sheaf H.sheaf) (x : AnalyticFrameTransitions.frameAnalyticOpen V.presentation q.source),
      D.coefficient q.source q.target ⟨x.val, x.property, x.property⟩ =
        E.coefficient q.source q.target ⟨x.val, x.property, x.property⟩) : D = E := by
  apply Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.ext V
  intro r s
  apply ContMDiffMap.ext
  intro x
  obtain ⟨q, hq⟩ := CommonLineFrames.tripleLineFrames_cover L K H (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  apply mul_left_cancel₀ (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation r q.source ⟨x.val, x.property.1, hq⟩)
  exact (D.frame_change r q.source s q.target x.val x.property ⟨hq, hq⟩).trans
    ((congrArg (fun a => a * AnalyticFrameTransitions.framePointTransition V.presentation s q.target x.val x.property.2 hq)
      (he q ⟨x.val, hq⟩)).trans
        (E.frame_change r q.source s q.target x.val x.property ⟨hq, hq⟩).symm)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorFrame_ext {D E : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V (L.tensor H) (K.tensor H)}
    (he : ∀ (q : CommonLineFrames.TripleLineFrame L.sheaf K.sheaf H.sheaf) (x : AnalyticFrameTransitions.frameAnalyticOpen V.presentation q.source),
      D.coefficient q.tensorSource q.tensorTarget ⟨x.val, x.property, x.property⟩ =
        E.coefficient q.tensorSource q.tensorTarget ⟨x.val, x.property, x.property⟩) : D = E := by
  apply Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.ext V
  intro r s
  apply ContMDiffMap.ext
  intro x
  obtain ⟨q, hq⟩ := CommonLineFrames.tripleLineFrames_cover L K H (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x.val)
  apply mul_left_cancel₀ (AnalyticFrameTransitions.frameTransitionPair_ne_zero V.presentation r q.tensorSource ⟨x.val, x.property.1, hq⟩)
  exact (D.frame_change r q.tensorSource s q.tensorTarget x.val x.property ⟨hq, hq⟩).trans
    ((congrArg (fun a => a * AnalyticFrameTransitions.framePointTransition V.presentation s q.tensorTarget x.val x.property.2 hq)
      (he q ⟨x.val, hq⟩)).trans
        (E.frame_change r q.tensorSource s q.tensorTarget x.val x.property ⟨hq, hq⟩).symm)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensor_injective :
    Function.Injective (fun D : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V L K => D.tensor H) := by
  intro D E h
  apply Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tripleFrame_ext H
  intro q x
  exact (D.tensor_induced_coefficient H q x).symm.trans
    ((congrArg (fun B : Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients V (L.tensor H) (K.tensor H) =>
      B.coefficient q.tensorSource q.tensorTarget ⟨x.val, x.property, x.property⟩) h).trans
        (E.tensor_induced_coefficient H q x))

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.algebraic_tensor_induced_coefficient (f : L.sheaf ⟶ K.sheaf)
    (q : CommonLineFrames.TripleLineFrame L.sheaf K.sheaf H.sheaf) (x : AnalyticFrameTransitions.frameAnalyticOpen V.presentation q.source) :
    LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient V (HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H.sheaf))
      q.tensorSource q.tensorTarget ⟨x.val, x.property, x.property⟩ =
    LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient V f q.source q.target ⟨x.val, x.property, x.property⟩ := by
  have h := LineMorphismTensorCoordinates.lineMorphismCoefficient_tensor f q.domain q.domain le_rfl q.sourceFrame q.targetFrame q.tensorFrame
  exact (LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient_value_on_open V (HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H.sheaf))
    q.tensorSource q.tensorTarget q.domain le_rfl le_rfl x.val x.property).trans
    ((congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.val.left q.domain x.property) h).trans
      (LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient_value_on_open V f q.source q.target q.domain
        le_rfl le_rfl x.val x.property).symm)

theorem Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensor_of_algebraic (f : L.sheaf ⟶ K.sheaf) :
    (Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L K f).tensor H =
      Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V (L.tensor H) (K.tensor H)
        (HilbertConstruction.Tensor.Bifunctor.tensorModuleMap f (𝟙 H.sheaf)) := by
  apply Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.tensorFrame_ext H
  intro q x
  exact ((Holomorphic.LineMorphismCoefficients.holomorphicLineMorphismCoefficientsOfAlgebraic V L K f).tensor_induced_coefficient H q x).trans
    (Holomorphic.LineMorphismCoefficients.HolomorphicLineMorphismCoefficients.algebraic_tensor_induced_coefficient H f q x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
