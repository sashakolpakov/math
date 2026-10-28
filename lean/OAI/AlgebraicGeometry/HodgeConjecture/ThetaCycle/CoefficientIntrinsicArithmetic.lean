import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallArithmetic

/-! # Coefficient Intrinsic Arithmetic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientIntrinsicArithmetic.CM

noncomputable section

/-! Native arithmetic data from explicit CM multiplicity coefficients
and their signs. This keeps the imaginary generator and all place maps
fixed when the rational orthogonal multiplicity basis changes. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K)
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (a : Fin 2 → K) (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)
  (s : Fin 2 → Fin places.count → Bool) (hμ : ∀ j, s j places.distinguished = true)
  (hs : ∀ j v, if s j v = true then (HeckeCycles.ReferenceDatum.CM.embeddings K places v (δ * a j)).im < 0
    else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K places v (δ * a j)).im)

include hs in
theorem coefficient_native_skew_sign (v : Fin places.count) (j : Fin 2) :
    (if 0 < CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a v j then (1 : ℂ) else -1) * Complex.I =
      if !(s j v) then Complex.I else -Complex.I := by
  have h := hs j v
  cases hd : s j v
  · simp only [hd, Bool.false_eq_true, ite_false] at h
    have hp : 0 < CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a v j := mul_pos (by norm_num) h
    simp [hp]
  · simp only [hd, ite_true] at h
    have hp : ¬ 0 < CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a v j := by
      change ¬ 0 < 2 * (HeckeCycles.ReferenceDatum.CM.embeddings K places v (δ * a j)).im
      linarith
    simp [hp]

def sourceCoefficientArithmetic :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 2
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
      (BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0) where
  places := places.count
  enumerate := RealPlaces.CM.sourceRealPlaces K places
  distinguished := places.distinguished
  other_place := BallArithmetic.CM.source_other_place K places B.other_place
  real := CMArchimedeanCoordinates.CM.sourceRealCoordinate K places
  real_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_continuous K places
  real_inverse_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_inverse_continuous K places
  complex := CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0
  complex_continuous := CMArchimedeanCoordinates.CM.source_complex_coordinate_continuous K places δ hδ hδ0
  complex_inverse_continuous := CMArchimedeanCoordinates.CM.source_complex_coordinate_inverse_continuous K places δ hδ hδ0
  complex_scalar := CMArchimedeanCoordinates.CM.source_complex_coordinate_scalar K places δ hδ hδ0
  complex_star := CMArchimedeanCoordinates.CM.source_complex_coordinate_star K places δ hδ hδ0
  basisV := CMOrthonormalFrames.CM.sourceHermitianNormalizer K places B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B)
  basisP := CMOrthonormalFrames.CM.sourceSkewNormalizer K places δ hδ hδ0 a ha ha0
  positive v j := !(s j v)
  distinguished_sign j := by simp [hμ j]
  formV v := (BallArithmetic.CM.direct_source_hermitian_normalized K places δ hδ hδ0 B.b B.conjugate_b
    (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) v).trans
      (congrArg Matrix.diagonal (funext (CMOrthonormalFrames.CM.source_ball_hermitian_sign K places B v)))
  formP v := (BallArithmetic.CM.direct_source_skew_normalized K places δ hδ hδ0 a ha ha0 v).trans
    (congrArg Matrix.diagonal (funext (coefficient_native_skew_sign K places δ a s hs v)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientIntrinsicArithmetic.CM
