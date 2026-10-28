import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceComponents
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicBall

/-! # Source Scales -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceScales.CM

noncomputable section

/-! The actual source-to-native tensor normalization is diagonal with
explicit nonzero real scales at every original CM place. -/

open scoped Classical _root_.NumberField Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem native_complex_diagonal_normalizer_inv {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℝ) (hr : ∀ i, r i ≠ 0) :
    (DiagonalNormalization.CM.complexDiagonalNormalizer r hr).inv = Matrix.diagonal (fun i => (Real.sqrt |r i| : ℂ)) := by
  simp [DiagonalNormalization.CM.complexDiagonalNormalizer, DiagonalFrame.CM.diagonalMatrixUnit, DiagonalNormalization.CM.diagonalNormalizationScale]

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (places : HeckeCycles.GeometricSource.CM.Places K)

def sourceNativePlaceRadius (β : K) (v : Fin places.count) : ℝ :=
  Real.sqrt |(HeckeCycles.ReferenceDatum.CM.embeddings K places v β).re|

def sourceNativeMultiplicityScale (δ : K) (a : Fin 2 → K) (v : Fin places.count) (j : Fin 2) : ℝ :=
  Real.sqrt |CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a v j|

theorem source_native_place_radius_active (B : HeckeCycles.GeometricSource.CM.BallDatum K) :
    sourceNativePlaceRadius K places B.b places.distinguished = SourceIntrinsicBall.CM.sourceBallRadius K B := by
  rw [sourceNativePlaceRadius, HeckeCycles.ReferenceDatum.CM.embeddings_distinguished]
  change Real.sqrt |(B.b : ℂ).re| = Real.sqrt (-(B.b : ℂ).re)
  rw [abs_of_neg B.negative]

theorem source_native_place_radius_pos (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) (v : Fin places.count) :
    0 < sourceNativePlaceRadius K places β v := by
  apply Real.sqrt_pos.mpr
  apply abs_pos.mpr
  have h := CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero K places β hβ hβ0 v 2
  simpa only [CMFormCoordinates.CM.sourceHermitianRealCoefficients, ite_true] using h

theorem source_hermitian_normalizer_inv (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) (v : Fin places.count) :
    (CMOrthonormalFrames.CM.sourceHermitianNormalizer K places β hβ hβ0 v).inv =
      Matrix.diagonal (fun j => if j = 2 then (sourceNativePlaceRadius K places β v : ℂ) else 1) := by
  rw [CMOrthonormalFrames.CM.sourceHermitianNormalizer, native_complex_diagonal_normalizer_inv]
  congr 1
  funext j
  by_cases hj : j = 2 <;> simp [CMFormCoordinates.CM.sourceHermitianRealCoefficients, sourceNativePlaceRadius, hj]

variable (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (a : Fin 2 → K) (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)

include hδ hδ0 ha ha0 in
theorem source_native_multiplicity_scale_pos (v : Fin places.count) (j : Fin 2) :
    0 < sourceNativeMultiplicityScale K places δ a v j :=
  Real.sqrt_pos.mpr (abs_pos.mpr (CMFormCoordinates.CM.source_skew_coefficients_ne_zero K places δ hδ hδ0 a ha ha0 v j))

theorem source_skew_normalizer_inv (v : Fin places.count) :
    (CMOrthonormalFrames.CM.sourceSkewNormalizer K places δ hδ hδ0 a ha ha0 v).inv =
      Matrix.diagonal (fun j => (sourceNativeMultiplicityScale K places δ a v j : ℂ)) := by
  rw [CMOrthonormalFrames.CM.sourceSkewNormalizer, native_complex_diagonal_normalizer_inv]
  rfl

def sourceNativeTensorScale (β : K) (v : Fin places.count) (ij : Fin 3 × Fin 2) : ℝ :=
  (if ij.1 = 2 then sourceNativePlaceRadius K places β v else 1) *
    sourceNativeMultiplicityScale K places δ a v ij.2

include hδ hδ0 ha ha0 in
theorem source_native_tensor_scale_pos (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
    (v : Fin places.count) (ij : Fin 3 × Fin 2) :
    0 < sourceNativeTensorScale K places δ a β v ij := by
  apply mul_pos _ (source_native_multiplicity_scale_pos K places δ hδ hδ0 a ha ha0 v ij.2)
  split_ifs
  · exact source_native_place_radius_pos K places β hβ hβ0 v
  · exact zero_lt_one

theorem source_tensor_normalizer_diagonal (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) (v : Fin places.count) :
    (CMOrthonormalFrames.CM.sourceHermitianNormalizer K places β hβ hβ0 v).inv ⊗ₖ
      (CMOrthonormalFrames.CM.sourceSkewNormalizer K places δ hδ hδ0 a ha ha0 v).inv =
      Matrix.diagonal (fun ij => (sourceNativeTensorScale K places δ a β v ij : ℂ)) := by
  rw [source_hermitian_normalizer_inv, source_skew_normalizer_inv, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext ij
  simp only [sourceNativeTensorScale, Complex.ofReal_mul, apply_ite, Complex.ofReal_one]

omit places δ hδ hδ0 a ha ha0 in
theorem direct_source_tensor_normalizer {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (Q : Lagrangians.CM.LagrangianPair K B places d)
    (hμ : ∀ j, d j places.distinguished = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) (v : Fin places.count) :
    IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) v =
      Matrix.diagonal (fun ij => (sourceNativeTensorScale K places Q.delta Q.a B.b v ij : ℂ)) :=
  source_tensor_normalizer_diagonal K places Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) B.b B.conjugate_b
    (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) v

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceScales.CM
