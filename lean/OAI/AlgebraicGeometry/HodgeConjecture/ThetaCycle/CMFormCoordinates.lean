import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMArchimedeanCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMGlobalFrames

/-! # CM Form Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMFormCoordinates.CM

noncomputable section

/-! ThetaCycle: the actual localized Hermitian and skew-Hermitian matrices in
the explicitly chosen complex coordinates. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [IsCMField K] (places : HeckeCycles.GeometricSource.CM.Places K)
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem source_localized_matrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n)
      (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))
    (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K) M (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
        (CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i) =
      fun j k => star (HeckeCycles.ReferenceDatum.CM.embeddings K places i (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0 (M j k))) := by
  ext j k
  change CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal _ _ _ (M j k)) = _
  rw [CMArchimedeanCoordinates.CM.source_conjugate_complex_coordinate_apply, CMArchimedeanCoordinates.CM.source_complex_coordinate_rational]

theorem source_fixed_element_real (x : K) (hx : IsCMField.complexConj K x = x)
    (i : Fin places.count) : (HeckeCycles.ReferenceDatum.CM.embeddings K places i x).im = 0 := by
  have h := IsCMField.complexEmbedding_complexConj K (HeckeCycles.ReferenceDatum.CM.embeddings K places i).toRingHom x
  rw [hx] at h
  have hi := congrArg Complex.im h
  change (HeckeCycles.ReferenceDatum.CM.embeddings K places i x).im = -(HeckeCycles.ReferenceDatum.CM.embeddings K places i x).im at hi
  linarith

theorem source_fixed_element_eq_real (x : K) (hx : IsCMField.complexConj K x = x)
    (i : Fin places.count) : ((HeckeCycles.ReferenceDatum.CM.embeddings K places i x).re : ℂ) = HeckeCycles.ReferenceDatum.CM.embeddings K places i x := by
  apply Complex.ext
  · rfl
  · exact (source_fixed_element_real K places x hx i).symm

def sourceHermitianRealCoefficients (β : K) (i : Fin places.count) : Fin 3 → ℝ :=
  fun j => if j = 2 then (HeckeCycles.ReferenceDatum.CM.embeddings K places i β).re else 1

def sourceSkewRealCoefficients (a : Fin 2 → K) (i : Fin places.count) : Fin 2 → ℝ :=
  fun j => 2 * (HeckeCycles.ReferenceDatum.CM.embeddings K places i (δ * a j)).im

theorem source_hermitian_local_matrix (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
    (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
        (CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i) =
      Matrix.diagonal (fun j => (sourceHermitianRealCoefficients K places β i j : ℂ)) := by
  rw [CMGlobalFrames.CM.cm_hermitian_unit_val K δ hδ hδ0 β hβ hβ0, source_localized_matrix]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp only [QuadraticTensor.CM.quadraticHermitianMatrix, Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    by_cases hj : j = 2
    · simp only [hj, ite_true, sourceHermitianRealCoefficients]
      rw [← source_fixed_element_eq_real K places β hβ i]
      exact Complex.conj_ofReal _
    · simp [hj, sourceHermitianRealCoefficients]
  · simp [QuadraticTensor.CM.quadraticHermitianMatrix, hjk]

theorem source_skew_local_matrix (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)
    (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmSkewUnit K δ hδ hδ0 a ha ha0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
        (CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i) =
      Matrix.diagonal (fun j => (sourceSkewRealCoefficients K places δ a i j : ℂ) * Complex.I) := by
  have him (j : Fin 2) : IsCMField.complexConj K (δ * a j) = -(δ * a j) := by
    rw [map_mul, hδ, ha]
    ring
  rw [CMGlobalFrames.CM.cm_skew_unit_val K δ hδ hδ0 a ha ha0, source_localized_matrix]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp only [QuadraticTensor.CM.quadraticSkewMatrix, Matrix.diagonal_apply_eq, AlgEquiv.apply_symm_apply]
    have hz := CMArchimedeanCoordinates.CM.source_imaginary_real_zero K places (δ * a j) (him j) i
    rw [show -2 * δ * a j = -2 * (δ * a j) by ring, map_mul, map_neg, map_ofNat]
    apply Complex.ext
    · have hz' : (HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).re * (HeckeCycles.ReferenceDatum.CM.embeddings K places i (a j)).re -
          (HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).im * (HeckeCycles.ReferenceDatum.CM.embeddings K places i (a j)).im = 0 := by
        simpa only [map_mul, Complex.mul_re] using hz
      simp [sourceSkewRealCoefficients, Complex.mul_re, hz']
    · simp [sourceSkewRealCoefficients, Complex.mul_im]
      ring
  · simp [QuadraticTensor.CM.quadraticSkewMatrix, hjk]

theorem source_hermitian_coefficients_ne_zero (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) (i : Fin places.count) :
    ∀ j, sourceHermitianRealCoefficients K places β i j ≠ 0 := by
  intro j
  by_cases hj : j = 2
  · simp only [sourceHermitianRealCoefficients, hj, ite_true]
    intro h
    apply hβ0
    apply (HeckeCycles.ReferenceDatum.CM.embeddings K places i).injective
    rw [map_zero]
    exact Complex.ext h (source_fixed_element_real K places β hβ i)
  · simp [sourceHermitianRealCoefficients, hj]

include hδ hδ0 in
theorem source_skew_coefficients_ne_zero (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)
    (i : Fin places.count) : ∀ j, sourceSkewRealCoefficients K places δ a i j ≠ 0 := by
  intro j
  apply mul_ne_zero (by norm_num)
  apply CMArchimedeanCoordinates.CM.source_imaginary_im_ne_zero K places (δ * a j) _ (mul_ne_zero hδ0 (ha0 j)) i
  rw [map_mul, hδ, ha]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMFormCoordinates.CM
