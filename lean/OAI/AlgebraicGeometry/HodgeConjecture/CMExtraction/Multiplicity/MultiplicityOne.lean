import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneBall
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneTrace

/-! # Multiplicity One -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.MultiplicityOne.Quadratic

noncomputable section

/-! Original CM embeddings with the opposite trace coefficient. Swapping
position and momentum then gives the native rational symplectic pairing.
This keeps the standard unitary action at the original embedding. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (places : HeckeCycles.GeometricSource.CM.Places E)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)

include ha in
theorem singleNegCoefficient_real : IsCMField.complexConj E (-a) = -a := by rw [map_neg, ha]

def directSkewUnit := OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 (-a)
  (singleNegCoefficient_real E a ha) (neg_ne_zero.mpr ha0)

variable [IsGalois ℚ E]

theorem directHermitian_local (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E)
      (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val (.inl (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places i))).map
        (ThetaCycle.CMArchimedeanCoordinates.CM.sourceComplexCoordinate E places δ hδ hδ0 i) =
      Matrix.diagonal (fun j => (ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients E places b i j : ℂ)) := by
  rw [ThetaCycle.CMGlobalFrames.CM.cm_hermitian_unit_val E δ hδ hδ0]
  apply Matrix.ext
  intro j k
  change ThetaCycle.CMArchimedeanCoordinates.CM.sourceComplexCoordinate E places δ hδ hδ0 i
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal _ _ _ (ThetaCycle.QuadraticTensor.CM.quadraticHermitianMatrix E δ hδ hδ0 b j k)) = _
  rw [ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_rational]
  by_cases hjk : j = k
  · subst k
    simp only [ThetaCycle.QuadraticTensor.CM.quadraticHermitianMatrix, Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    by_cases hj : j = 2
    · simp only [hj, ite_true, ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients]
      exact (ThetaCycle.CMFormCoordinates.CM.source_fixed_element_eq_real E places b hb i).symm
    · simp [hj, ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients]
  · simp [ThetaCycle.QuadraticTensor.CM.quadraticHermitianMatrix, hjk]

theorem directSkew_local (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E)
      (directSkewUnit E δ hδ hδ0 a ha ha0).val (.inl (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places i))).map
        (ThetaCycle.CMArchimedeanCoordinates.CM.sourceComplexCoordinate E places δ hδ hδ0 i) =
      Matrix.diagonal (fun _ : Fin 1 => (OneLocal.Quadratic.singleSkewRealCoefficient E places δ a i : ℂ) * Complex.I) := by
  apply Matrix.ext
  intro j k
  have hjk : j = k := Subsingleton.elim _ _
  subst k
  change ThetaCycle.CMArchimedeanCoordinates.CM.sourceComplexCoordinate E places δ hδ hδ0 i
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal _ _ _ ((directSkewUnit E δ hδ hδ0 a ha ha0).val j j)) = _
  rw [ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_rational]
  change HeckeCycles.ReferenceDatum.CM.embeddings E places i ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0)
    ((OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 (-a) (singleNegCoefficient_real E a ha)
      (neg_ne_zero.mpr ha0)).val j j)) = _
  rw [OneFrames.Quadratic.singleSkewUnit_evaluation, Matrix.diagonal_apply_eq,
    show -2 * δ * -a = 2 * (δ * a) by ring, map_mul, map_ofNat]
  have him : IsCMField.complexConj E (δ * a) = -(δ * a) := by rw [map_mul, hδ, ha, neg_mul]
  have hz := ThetaCycle.CMArchimedeanCoordinates.CM.source_imaginary_real_zero E places (δ * a) him i
  have he : HeckeCycles.ReferenceDatum.CM.embeddings E places i (δ * a) =
      ((HeckeCycles.ReferenceDatum.CM.embeddings E places i (δ * a)).im : ℂ) * Complex.I := by
    simpa only [hz, Complex.ofReal_zero, zero_add] using
      (Complex.re_add_im (HeckeCycles.ReferenceDatum.CM.embeddings E places i (δ * a))).symm
  calc
    _ = 2 * (((HeckeCycles.ReferenceDatum.CM.embeddings E places i (δ * a)).im : ℂ) * Complex.I) :=
      congrArg (fun z : ℂ => 2 * z) he
    _ = _ := by simp [OneLocal.Quadratic.singleSkewRealCoefficient, mul_assoc]

def directGlobalFrames : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 3 1
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (directSkewUnit E δ hδ hδ0 a ha ha0) :=
  OneFrames.Quadratic.singleGlobalFrames E δ hδ hδ0 b hb hb0 (-a)
    (singleNegCoefficient_real E a ha) (neg_ne_zero.mpr ha0)

def directBallArithmeticData
    (hball : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished b).re < 0)
    (hcompact : ∀ i, i ≠ places.distinguished → 0 < (HeckeCycles.ReferenceDatum.CM.embeddings E places i b).re)
    (hactive : (HeckeCycles.ReferenceDatum.CM.embeddings E places places.distinguished (δ * a)).im < 0)
    (hother : ∃ i : Fin places.count, i ≠ places.distinguished) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 1
      (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (directSkewUnit E δ hδ hδ0 a ha ha0) where
  places := places.count
  enumerate := ThetaCycle.RealPlaces.CM.sourceRealPlaces E places
  distinguished := places.distinguished
  other_place := hother
  real := ThetaCycle.CMArchimedeanCoordinates.CM.sourceRealCoordinate E places
  real_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_real_coordinate_continuous E places
  real_inverse_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_real_coordinate_inverse_continuous E places
  complex := ThetaCycle.CMArchimedeanCoordinates.CM.sourceComplexCoordinate E places δ hδ hδ0
  complex_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_continuous E places δ hδ hδ0
  complex_inverse_continuous := ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_inverse_continuous E places δ hδ hδ0
  complex_scalar := ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_scalar E places δ hδ hδ0
  complex_star := ThetaCycle.CMArchimedeanCoordinates.CM.source_complex_coordinate_star E places δ hδ hδ0
  basisV := ThetaCycle.CMOrthonormalFrames.CM.sourceHermitianNormalizer E places b hb hb0
  basisP := OneLocal.Quadratic.singleSkewNormalizer E places δ hδ hδ0 a ha ha0
  positive i _ := decide (0 < OneLocal.Quadratic.singleSkewRealCoefficient E places δ a i)
  distinguished_sign _ := by
    have hneg : OneLocal.Quadratic.singleSkewRealCoefficient E places δ a places.distinguished < 0 :=
      mul_neg_of_pos_of_neg (by norm_num) hactive
    simp [not_lt.mpr hneg.le]
  formV i := by
    rw [directHermitian_local]
    have h := ThetaCycle.DiagonalNormalization.CM.complex_diagonal_normalizer_form
      (ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients E places b i)
      (ThetaCycle.CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero E places b hb hb0 i) 1
    simp only [mul_one] at h
    exact h.trans (congrArg Matrix.diagonal
      (funext (OneBall.Quadratic.singleHermitian_sign E places b hball hcompact i)))
  formP i := by
    rw [directSkew_local]
    refine (ThetaCycle.DiagonalNormalization.CM.complex_diagonal_normalizer_form
      (fun _ : Fin 1 => OneLocal.Quadratic.singleSkewRealCoefficient E places δ a i)
      (fun _ => OneLocal.Quadratic.singleSkewRealCoefficient_ne_zero E places δ hδ hδ0 a ha ha0 i) Complex.I).trans ?_
    congr 1
    funext j
    by_cases h : 0 < OneLocal.Quadratic.singleSkewRealCoefficient E places δ a i <;> simp [h]

omit [IsGalois ℚ E] in
theorem direct_tensor_rational_trace (x y : Fin 3 → E) :
    Algebra.trace ℚ (maximalRealSubfield E)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 3 1
        (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0).val (directSkewUnit E δ hδ hδ0 a ha ha0).val
        (OneTrace.Quadratic.singleTensorPosition E δ hδ hδ0 x) (OneTrace.Quadratic.singleTensorPosition E δ hδ hδ0 y)) =
      -Algebra.trace ℚ E (δ * (a * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)) := by
  rw [directSkewUnit, OneTrace.Quadratic.single_tensor_rational_trace]
  rw [neg_mul, mul_neg, map_neg]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.MultiplicityOne.Quadratic
