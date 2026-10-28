import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneLocal
import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # One Ball -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneBall.Quadratic

noncomputable section

/-! Construct the multiplicity-one ball-arithmetic input from CM embeddings
and the actual Hermitian coefficients. All period, theta and oscillator
identifications remain conclusions of the full AdelicTheta prerequisite. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [IsCMField E]
  (places : HeckeCycles.GeometricSource.CM.Places E)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (hball : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re < 0)
  (hcompact : ∀ i, i ≠ places.distinguished → 0 < (HeckeCycles.ReferenceDatum.CM.embeddings E places i b).re)
  (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)
  (hactive : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished (δ * a)).im < 0)
  (hother : ∃ i : Fin places.count, i ≠ places.distinguished)

include hball hcompact in
theorem singleHermitian_sign (i : Fin places.count) (j : Fin 3) :
    (if 0 < ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients E places b i j then (1 : ℂ) else -1) =
      if i = places.distinguished ∧ j = 2 then -1 else 1 := by
  by_cases hj : j = 2
  · subst j
    by_cases hi : i = places.distinguished
    · subst i
      simp [ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients, not_lt.mpr hball.le]
    · simp [ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients, hi, hcompact i hi]
  · simp [ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients, hj]

def singleBallArithmeticData :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 1
      (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 a ha ha0) where
  places := places.count
  enumerate := ThetaCycle.RealPlaces.CM.sourceRealPlaces E places
  distinguished := places.distinguished
  other_place := hother
  real := ThetaCycle.CMArchimedeanCoordinates.CM.sourceRealCoordinate E places
  real_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_real_coordinate_continuous E places
  real_inverse_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_real_coordinate_inverse_continuous E places
  complex := ThetaCycle.CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate E places δ hδ hδ0
  complex_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_continuous E places δ hδ hδ0
  complex_inverse_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_inverse_continuous E places δ hδ hδ0
  complex_scalar := ThetaCycle.CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_scalar E places δ hδ hδ0
  complex_star := ThetaCycle.CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_star E places δ hδ hδ0
  basisV := ThetaCycle.CMOrthonormalFrames.CM.sourceHermitianNormalizer E places b hb hb0
  basisP := OneLocal.Quadratic.singleSkewNormalizer E places δ hδ hδ0 a ha ha0
  positive i _ := decide (0 < OneLocal.Quadratic.singleSkewRealCoefficient E places δ a i)
  distinguished_sign _ := by
    have hneg : OneLocal.Quadratic.singleSkewRealCoefficient E places δ a places.distinguished < 0 :=
      mul_neg_of_pos_of_neg (by norm_num) hactive
    simp [not_lt.mpr hneg.le]
  formV i :=
    (ThetaCycle.CMOrthonormalFrames.CM.source_hermitian_normalized E places δ hδ hδ0 b hb hb0 i).trans
      (congrArg Matrix.diagonal (funext (singleHermitian_sign E places b hball hcompact i)))
  formP i := by
    refine (OneLocal.Quadratic.singleSkewUnit_normalized E places δ hδ hδ0 a ha ha0 i).trans ?_
    congr 1
    funext j
    by_cases h : 0 < OneLocal.Quadratic.singleSkewRealCoefficient E places δ a i <;> simp [h]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneBall.Quadratic
