import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames

/-! # Single Line Arithmetic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineArithmetic.CM

noncomputable section

/-! One actual multiplicity line in the original CM embeddings, with
the opposite skew trace coefficient required by the native phase order. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (a : K) (ha : IsCMField.complexConj K a = a) (ha0 : a ≠ 0)

def directSingleLineSkewUnit :
    (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  CMOrthonormalFrames.CM.singleLineSkewUnit K δ hδ hδ0 (-a) (by rw [map_neg, ha]) (neg_ne_zero.mpr ha0)

theorem direct_single_line_skew_conjugate_transpose :
    (directSingleLineSkewUnit K δ hδ hδ0 a ha ha0).val.conjTranspose =
      -(directSingleLineSkewUnit K δ hδ hδ0 a ha ha0).val :=
  CMOrthonormalFrames.CM.single_line_skew_conjugate_transpose K δ hδ hδ0 (-a) (by rw [map_neg, ha]) (neg_ne_zero.mpr ha0)

def directSingleLineGlobalFrames (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 1
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0) (directSingleLineSkewUnit K δ hδ hδ0 a ha ha0) :=
  CMOrthonormalFrames.CM.singleLineGlobalFrames K δ hδ hδ0 (-a) (by rw [map_neg, ha]) (neg_ne_zero.mpr ha0) β hβ hβ0

theorem direct_single_line_skew_local_matrix (places : HeckeCycles.GeometricSource.CM.Places K) (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K) (directSingleLineSkewUnit K δ hδ hδ0 a ha ha0).val
      (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0 i) =
      Matrix.diagonal (fun j => (CMOrthonormalFrames.CM.singleLineSkewCoefficient K δ a places i j : ℂ) * Complex.I) := by
  apply Matrix.ext
  intro j k
  have hj : j = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst j k
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    (BallArithmetic.CM.direct_source_skew_local_matrix K places δ hδ hδ0 (fun _ => a) (fun _ => ha) (fun _ => ha0) i)

theorem direct_single_line_skew_normalized (places : HeckeCycles.GeometricSource.CM.Places K) (i : Fin places.count) :
    (CMOrthonormalFrames.CM.singleLineSkewNormalizer K δ hδ hδ0 a ha ha0 places i).val.conjTranspose *
      ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K) (directSingleLineSkewUnit K δ hδ hδ0 a ha ha0).val
        (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0 i)) *
      (CMOrthonormalFrames.CM.singleLineSkewNormalizer K δ hδ hδ0 a ha ha0 places i).val =
      Matrix.diagonal (fun j => (if 0 < CMOrthonormalFrames.CM.singleLineSkewCoefficient K δ a places i j then (1 : ℂ) else -1) * Complex.I) := by
  rw [direct_single_line_skew_local_matrix]
  exact DiagonalNormalization.CM.complex_diagonal_normalizer_form _ _ Complex.I

omit δ hδ hδ0 a ha ha0 in
def directSingleLineArithmetic {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (Q : Lagrangians.CM.LagrangianPair K B places d)
    (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary) 1
      (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
      (directSingleLineSkewUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
        (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j)) where
  places := places.count
  enumerate := RealPlaces.CM.sourceRealPlaces K places
  distinguished := places.distinguished
  other_place := BallArithmetic.CM.source_other_place K places B.other_place
  real := CMArchimedeanCoordinates.CM.sourceRealCoordinate K places
  real_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_continuous K places
  real_inverse_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_inverse_continuous K places
  complex := CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_continuous := CMArchimedeanCoordinates.CM.source_complex_coordinate_continuous K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_inverse_continuous := CMArchimedeanCoordinates.CM.source_complex_coordinate_inverse_continuous K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_scalar := CMArchimedeanCoordinates.CM.source_complex_coordinate_scalar K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_star := CMArchimedeanCoordinates.CM.source_complex_coordinate_star K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  basisV := CMOrthonormalFrames.CM.sourceHermitianNormalizer K places B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B)
  basisP := CMOrthonormalFrames.CM.singleLineSkewNormalizer K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
    (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j) places
  positive i _ := !(d j i)
  distinguished_sign _ := by simp [hμ j]
  formV i := (BallArithmetic.CM.direct_source_hermitian_normalized K places Q.delta Q.delta_imaginary Q.delta_ne_zero
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) i).trans
      (congrArg Matrix.diagonal (funext (CMOrthonormalFrames.CM.source_ball_hermitian_sign K places B i)))
  formP i := (direct_single_line_skew_normalized K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
    (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j) places i).trans
      (congrArg Matrix.diagonal (funext (fun _ => CMOrthonormalFrames.CM.source_lagrangian_skew_sign K places Q hμ i j)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineArithmetic.CM
