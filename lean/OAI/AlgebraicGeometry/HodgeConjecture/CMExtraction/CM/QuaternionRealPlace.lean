import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.RealSplit
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionSubgroup
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMArchimedeanCoordinates

/-! # Quaternion Real Place -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionRealPlace

noncomputable section

/-! The actual binary quaternion coefficient is positive at the retained
active real completion of the CM field. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMArchimedeanCoordinates.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

theorem cmQuaternion_second_coefficient_ne_zero
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0) :
    -Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb ≠ 0 := by
  apply neg_ne_zero.mpr
  intro h
  exact hb0 (congrArg (fun x : maximalRealSubfield E => (x : E)) h)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [IsCMField E]
  (places : HeckeCycles.GeometricSource.CM.Places E) (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

theorem cmQuaternion_active_real_positive
    (hball : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re < 0) :
    0 < ThetaCycle.CMArchimedeanCoordinates.CM.sourceRealCoordinate E places places.distinguished
      (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places places.distinguished))
        (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)) := by
  have he := congrArg Complex.re (ThetaCycle.CMArchimedeanCoordinates.CM.source_real_coordinate_rational E places places.distinguished
    (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb))
  change ThetaCycle.CMArchimedeanCoordinates.CM.sourceRealCoordinate E places places.distinguished
      (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places places.distinguished))
        (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)) =
      (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished (-b)).re at he
  have he' : ThetaCycle.CMArchimedeanCoordinates.CM.sourceRealCoordinate E places places.distinguished
      (NumberTheory.Quaternion.Arithmetic.LocalAdeles.localEmbedding (Sum.inl (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places places.distinguished))
        (-Geometry.ComplexBall.ArithmeticQuotientSplitUnitary.realCoefficient b hb)) =
      -(HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re := by
    simpa only [map_neg, Complex.neg_re] using he
  rw [he']
  exact neg_pos.mpr hball

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.QuaternionRealPlace
