import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames
import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Ball Arithmetic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallArithmetic.CM

noncomputable section

section

/-! ThetaCycle: construct the native AdelicTheta ball-arithmetic data from the actual
ball coefficient, CM representatives, and the two retained multiplicity
lines. No period, oscillator, or compatibility conclusion is a field here. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [IsCMField K]

omit [IsGalois ℚ K] in
theorem source_other_place (places : HeckeCycles.GeometricSource.CM.Places K)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) :
    ∃ i : Fin places.count, i ≠ places.distinguished := by
  obtain ⟨τ, hτ1, hτc⟩ := hother
  obtain ⟨⟨i, b⟩, hi⟩ := places.complete.2 τ
  refine ⟨i, ?_⟩
  intro he
  subst i
  cases b
  · exact hτ1 (hi.symm.trans places.identity)
  · apply hτc
    simpa only [ite_true, places.identity, mul_one] using hi.symm

def sourceBallArithmeticData {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (P : Lagrangians.CM.LagrangianPair K B places d)
    (hμ : ∀ j, d j places.distinguished = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K)
      (QuadraticModel.CM.cmQuadraticParameter K P.delta P.delta_imaginary) 2
      (CMGlobalFrames.CM.cmHermitianUnit K P.delta P.delta_imaginary B.b B.conjugate_b
        (fun hb => (ne_of_lt B.negative) (by simp [hb])))
      (CMGlobalFrames.CM.cmSkewUnit K P.delta P.delta_imaginary P.delta_ne_zero P.a
        (fun j => (P.a_sign j).2.1) (fun j => (P.a_sign j).1)) where
  places := places.count
  enumerate := RealPlaces.CM.sourceRealPlaces K places
  distinguished := places.distinguished
  other_place := source_other_place K places hother
  real := CMArchimedeanCoordinates.CM.sourceRealCoordinate K places
  real_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_continuous K places
  real_inverse_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_inverse_continuous K places
  complex := CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places P.delta P.delta_imaginary P.delta_ne_zero
  complex_continuous :=
    CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_continuous K places P.delta P.delta_imaginary P.delta_ne_zero
  complex_inverse_continuous :=
    CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_inverse_continuous K places P.delta P.delta_imaginary P.delta_ne_zero
  complex_scalar :=
    CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_scalar K places P.delta P.delta_imaginary P.delta_ne_zero
  complex_star :=
    CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_star K places P.delta P.delta_imaginary P.delta_ne_zero
  basisV := CMOrthonormalFrames.CM.sourceHermitianNormalizer K places B.b B.conjugate_b
    (fun hb => (ne_of_lt B.negative) (by simp [hb]))
  basisP := CMOrthonormalFrames.CM.sourceSkewNormalizer K places P.delta P.delta_imaginary P.delta_ne_zero P.a
    (fun j => (P.a_sign j).2.1) (fun j => (P.a_sign j).1)
  positive i j := !(d j i)
  distinguished_sign j := by simp [hμ j]
  formV i :=
    (CMOrthonormalFrames.CM.source_hermitian_normalized K places P.delta P.delta_imaginary P.delta_ne_zero B.b B.conjugate_b
      (fun hb => (ne_of_lt B.negative) (by simp [hb])) i).trans
        (congrArg Matrix.diagonal (funext (CMOrthonormalFrames.CM.source_ball_hermitian_sign K places B i)))
  formP i :=
    (CMOrthonormalFrames.CM.source_skew_normalized K places P.delta P.delta_imaginary P.delta_ne_zero P.a
      (fun j => (P.a_sign j).2.1) (fun j => (P.a_sign j).1) i).trans
        (congrArg Matrix.diagonal (funext (CMOrthonormalFrames.CM.source_lagrangian_skew_sign K places P hμ i)))

end

/-! Native data at the original CM embeddings. The opposite skew trace
coefficient compensates for the native position/momentum phase order. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

local instance directNativeRealNumberField (K : IntermediateField ℚ ℂ)
    [NumberField K] [IsCMField K] : NumberField (maximalRealSubfield K) := by
  infer_instance

theorem direct_source_ball_b_ne_zero (K : IntermediateField ℚ ℂ)
    [NumberField K] [IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K) : B.b ≠ 0 :=
  fun hb => (ne_of_lt B.negative) (by simp [hb])

theorem direct_source_a_fixed (K : IntermediateField ℚ ℂ)
    [NumberField K] [IsCMField K] [IsGalois ℚ K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (Q : Lagrangians.CM.LagrangianPair K B places d) :
    ∀ j, IsCMField.complexConj K (Q.a j) = Q.a j := fun j => (Q.a_sign j).2.1

theorem direct_source_a_ne_zero (K : IntermediateField ℚ ℂ)
    [NumberField K] [IsCMField K] [IsGalois ℚ K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (Q : Lagrangians.CM.LagrangianPair K B places d) :
    ∀ j, Q.a j ≠ 0 := fun j => (Q.a_sign j).1

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (places : HeckeCycles.GeometricSource.CM.Places K) (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem direct_source_localized_matrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))
    (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K) M (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
      (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0 i) =
      fun j k => HeckeCycles.ReferenceDatum.CM.embeddings K places i (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0 (M j k)) := by
  ext j k
  exact CMArchimedeanCoordinates.CM.source_complex_coordinate_rational K places δ hδ hδ0 i (M j k)

theorem direct_source_hermitian_local_matrix (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
        (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0 i) =
      Matrix.diagonal (fun j => (CMFormCoordinates.CM.sourceHermitianRealCoefficients K places β i j : ℂ)) := by
  rw [CMGlobalFrames.CM.cm_hermitian_unit_val K δ hδ hδ0, direct_source_localized_matrix]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp only [QuadraticTensor.CM.quadraticHermitianMatrix, Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    by_cases hj : j = 2
    · simp only [hj, ite_true, CMFormCoordinates.CM.sourceHermitianRealCoefficients]
      exact (CMFormCoordinates.CM.source_fixed_element_eq_real K places β hβ i).symm
    · simp [hj, CMFormCoordinates.CM.sourceHermitianRealCoefficients]
  · simp [QuadraticTensor.CM.quadraticHermitianMatrix, hjk]

variable (a : Fin 2 → K) (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)

def directSourceSkewUnit :
    (Matrix (Fin 2) (Fin 2) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  CMGlobalFrames.CM.cmSkewUnit K δ hδ hδ0 (fun j => -a j)
    (fun j => by rw [map_neg, ha j]) (fun j => neg_ne_zero.mpr (ha0 j))

theorem direct_source_skew_local_matrix (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
      (directSourceSkewUnit K δ hδ hδ0 a ha ha0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
        (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0 i) =
      Matrix.diagonal (fun j => (CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a i j : ℂ) * Complex.I) := by
  rw [directSourceSkewUnit, CMGlobalFrames.CM.cm_skew_unit_val K δ hδ hδ0, direct_source_localized_matrix]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp only [QuadraticTensor.CM.quadraticSkewMatrix, Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    have him : IsCMField.complexConj K (δ * a j) = -(δ * a j) := by rw [map_mul, hδ, ha, neg_mul]
    have hz := CMArchimedeanCoordinates.CM.source_imaginary_real_zero K places (δ * a j) him i
    rw [show -2 * δ * -a j = 2 * (δ * a j) by ring, map_mul, map_ofNat]
    have he : HeckeCycles.ReferenceDatum.CM.embeddings K places i (δ * a j) =
        ((HeckeCycles.ReferenceDatum.CM.embeddings K places i (δ * a j)).im : ℂ) * Complex.I := by
      simpa only [hz, Complex.ofReal_zero, zero_add] using
        (Complex.re_add_im (HeckeCycles.ReferenceDatum.CM.embeddings K places i (δ * a j))).symm
    rw [he]
    simp only [CMFormCoordinates.CM.sourceSkewRealCoefficients, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc]
  · simp [QuadraticTensor.CM.quadraticSkewMatrix, hjk]

def directSourceGlobalFrames (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0) (directSourceSkewUnit K δ hδ hδ0 a ha ha0) :=
  CMGlobalFrames.CM.cmGlobalFrames K δ hδ hδ0 β hβ hβ0 (fun j => -a j)
    (fun j => by rw [map_neg, ha j]) (fun j => neg_ne_zero.mpr (ha0 j))

theorem direct_source_hermitian_normalized (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) (i : Fin places.count) :
    (CMOrthonormalFrames.CM.sourceHermitianNormalizer K places β hβ hβ0 i).val.conjTranspose *
      ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K) (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val
        (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0 i)) *
      (CMOrthonormalFrames.CM.sourceHermitianNormalizer K places β hβ hβ0 i).val =
      Matrix.diagonal (fun j => if 0 < CMFormCoordinates.CM.sourceHermitianRealCoefficients K places β i j then (1 : ℂ) else -1) := by
  rw [direct_source_hermitian_local_matrix]
  simpa only [CMOrthonormalFrames.CM.sourceHermitianNormalizer, mul_one] using! DiagonalNormalization.CM.complex_diagonal_normalizer_form
    (CMFormCoordinates.CM.sourceHermitianRealCoefficients K places β i)
    (CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero K places β hβ hβ0 i) 1

theorem direct_source_skew_normalized (i : Fin places.count) :
    (CMOrthonormalFrames.CM.sourceSkewNormalizer K places δ hδ hδ0 a ha ha0 i).val.conjTranspose *
      ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K) (directSourceSkewUnit K δ hδ hδ0 a ha ha0).val
        (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map (CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places δ hδ hδ0 i)) *
      (CMOrthonormalFrames.CM.sourceSkewNormalizer K places δ hδ hδ0 a ha ha0 i).val =
      Matrix.diagonal (fun j => (if 0 < CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a i j
        then (1 : ℂ) else -1) * Complex.I) := by
  rw [direct_source_skew_local_matrix]
  exact DiagonalNormalization.CM.complex_diagonal_normalizer_form _ _ Complex.I

omit places δ hδ hδ0 a ha ha0 in
def directSourceBallArithmeticData {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Fin places.count → Bool} (Q : Lagrangians.CM.LagrangianPair K B places d)
    (hμ : ∀ j, d j places.distinguished = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary) 2
      (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b
        (direct_source_ball_b_ne_zero K B))
      (directSourceSkewUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
        (direct_source_a_fixed K Q) (direct_source_a_ne_zero K Q)) where
  places := places.count
  enumerate := RealPlaces.CM.sourceRealPlaces K places
  distinguished := places.distinguished
  other_place := source_other_place K places hother
  real := CMArchimedeanCoordinates.CM.sourceRealCoordinate K places
  real_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_continuous K places
  real_inverse_continuous := CMArchimedeanCoordinates.CM.source_real_coordinate_inverse_continuous K places
  complex := CMArchimedeanCoordinates.CM.sourceComplexCoordinate K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_continuous := CMArchimedeanCoordinates.CM.source_complex_coordinate_continuous K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_inverse_continuous := CMArchimedeanCoordinates.CM.source_complex_coordinate_inverse_continuous K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_scalar := CMArchimedeanCoordinates.CM.source_complex_coordinate_scalar K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  complex_star := CMArchimedeanCoordinates.CM.source_complex_coordinate_star K places Q.delta Q.delta_imaginary Q.delta_ne_zero
  basisV := CMOrthonormalFrames.CM.sourceHermitianNormalizer K places B.b B.conjugate_b
    (direct_source_ball_b_ne_zero K B)
  basisP := CMOrthonormalFrames.CM.sourceSkewNormalizer K places Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
    (direct_source_a_fixed K Q) (direct_source_a_ne_zero K Q)
  positive i j := !(d j i)
  distinguished_sign j := by simp [hμ j]
  formV i :=
    (direct_source_hermitian_normalized K places Q.delta Q.delta_imaginary Q.delta_ne_zero
      B.b B.conjugate_b (direct_source_ball_b_ne_zero K B) i).trans
      (congrArg Matrix.diagonal (funext (CMOrthonormalFrames.CM.source_ball_hermitian_sign K places B i)))
  formP i :=
    (direct_source_skew_normalized K places Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
      (direct_source_a_fixed K Q) (direct_source_a_ne_zero K Q) i).trans
      (congrArg Matrix.diagonal (funext (CMOrthonormalFrames.CM.source_lagrangian_skew_sign K places Q hμ i)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallArithmetic.CM
