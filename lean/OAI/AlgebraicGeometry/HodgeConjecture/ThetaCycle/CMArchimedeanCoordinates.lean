import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealPlaces
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealQuadraticCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational

/-! # CM Archimedean Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMArchimedeanCoordinates.CM

noncomputable section

/-! ThetaCycle: real and complex local coordinates from the actual CM field,
chosen embedding representatives, and retained imaginary trace coefficient. -/

open scoped Classical _root_.NumberField
open _root_.NumberField _root_.NumberField.InfinitePlace _root_.NumberField.InfinitePlace.Completion
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [IsCMField K] (places : HeckeCycles.GeometricSource.CM.Places K)

def sourceRealCoordinate (i : Fin places.count) :
    (RealPlaces.CM.sourceRealPlaces K places i).Completion ≃+* ℝ :=
  ringEquivRealOfIsReal (IsTotallyReal.isReal (RealPlaces.CM.sourceRealPlaces K places i))

theorem source_real_coordinate_continuous (i : Fin places.count) :
    Continuous (sourceRealCoordinate K places i) :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal (RealPlaces.CM.sourceRealPlaces K places i))).continuous

theorem source_real_coordinate_inverse_continuous (i : Fin places.count) :
    Continuous (sourceRealCoordinate K places i).symm :=
  (isometryEquivRealOfIsReal (IsTotallyReal.isReal (RealPlaces.CM.sourceRealPlaces K places i))).symm.continuous

theorem source_real_coordinate_rational (i : Fin places.count) (x : maximalRealSubfield K) :
    (sourceRealCoordinate K places i
      (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) (.inl (RealPlaces.CM.sourceRealPlaces K places i)) x) : ℂ) =
        HeckeCycles.ReferenceDatum.CM.embeddings K places i (x : K) := by
  change (extensionEmbeddingOfIsReal (IsTotallyReal.isReal (RealPlaces.CM.sourceRealPlaces K places i))
    (algebraMap (maximalRealSubfield K) (RealPlaces.CM.sourceRealPlaces K places i).Completion x) : ℂ) = _
  simpa using RealPlaces.CM.source_real_embedding K places i x

variable (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

include hδ in
theorem source_imaginary_real_zero (i : Fin places.count) :
    (HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).re = 0 := by
  have hc := IsCMField.complexEmbedding_complexConj K (HeckeCycles.ReferenceDatum.CM.embeddings K places i).toRingHom δ
  rw [hδ, map_neg] at hc
  have h := congrArg Complex.re hc
  simp only [Complex.neg_re, Complex.conj_re] at h
  change -(HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).re = (HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).re at h
  linarith

include hδ hδ0 in
theorem source_imaginary_im_ne_zero (i : Fin places.count) :
    (HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).im ≠ 0 := by
  intro h
  apply hδ0
  apply (HeckeCycles.ReferenceDatum.CM.embeddings K places i).injective
  rw [map_zero]
  exact Complex.ext (source_imaginary_real_zero K places δ hδ i) h

theorem source_quadratic_parameter_real (i : Fin places.count) :
    sourceRealCoordinate K places i
      (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) (.inl (RealPlaces.CM.sourceRealPlaces K places i))
        (QuadraticModel.CM.cmQuadraticParameter K δ hδ)) = -((HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).im ^ 2) := by
  have h := congrArg Complex.re
    (source_real_coordinate_rational K places i (QuadraticModel.CM.cmQuadraticParameter K δ hδ))
  change _ = (HeckeCycles.ReferenceDatum.CM.embeddings K places i (δ ^ 2)).re at h
  rw [map_pow] at h
  simpa only [Complex.ofReal_re, pow_two, Complex.mul_re,
    source_imaginary_real_zero K places δ hδ i, zero_mul, zero_sub] using h

def sourceComplexCoordinate (i : Fin places.count) :
    RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
      (.inl (RealPlaces.CM.sourceRealPlaces K places i)) ≃+* ℂ :=
  RealQuadraticCoordinates.CM.realQuadraticComplexEquiv (sourceRealCoordinate K places i) _ (HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).im
    (source_quadratic_parameter_real K places δ hδ i)
    (source_imaginary_im_ne_zero K places δ hδ hδ0 i)

theorem source_complex_coordinate_continuous (i : Fin places.count) :
    Continuous (sourceComplexCoordinate K places δ hδ hδ0 i) :=
  RealQuadraticCoordinates.CM.real_quadratic_complex_continuous _ _ _ _ _ (source_real_coordinate_continuous K places i)

theorem source_complex_coordinate_inverse_continuous (i : Fin places.count) :
    Continuous (sourceComplexCoordinate K places δ hδ hδ0 i).symm :=
  RealQuadraticCoordinates.CM.real_quadratic_complex_inverse_continuous _ _ _ _ _
    (source_real_coordinate_inverse_continuous K places i)

theorem source_complex_coordinate_scalar (i : Fin places.count)
    (x : (RealPlaces.CM.sourceRealPlaces K places i).Completion) :
    sourceComplexCoordinate K places δ hδ hδ0 i (algebraMap _ _ x) =
      (sourceRealCoordinate K places i x : ℂ) :=
  RealQuadraticCoordinates.CM.real_quadratic_complex_scalar _ _ _ _ _ x

theorem source_complex_coordinate_star (i : Fin places.count)
    (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
      (.inl (RealPlaces.CM.sourceRealPlaces K places i))) :
    sourceComplexCoordinate K places δ hδ hδ0 i (star x) =
      star (sourceComplexCoordinate K places δ hδ hδ0 i x) :=
  RealQuadraticCoordinates.CM.real_quadratic_complex_star _ _ _ _ _ x

theorem source_complex_coordinate_rational (i : Fin places.count)
    (x : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)) :
    sourceComplexCoordinate K places δ hδ hδ0 i
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
        (.inl (RealPlaces.CM.sourceRealPlaces K places i)) x) =
      HeckeCycles.ReferenceDatum.CM.embeddings K places i (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0 x) := by
  have hδc : HeckeCycles.ReferenceDatum.CM.embeddings K places i δ = ((HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using source_imaginary_real_zero K places δ hδ i
    · simp
  change (sourceRealCoordinate K places i (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K)
    (.inl (RealPlaces.CM.sourceRealPlaces K places i)) x.re) : ℂ) +
    (sourceRealCoordinate K places i (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K)
      (.inl (RealPlaces.CM.sourceRealPlaces K places i)) x.im) : ℂ) *
      ((HeckeCycles.ReferenceDatum.CM.embeddings K places i δ).im : ℂ) * Complex.I =
        HeckeCycles.ReferenceDatum.CM.embeddings K places i (QuadraticModel.CM.cmQuadraticMap K δ hδ x)
  rw [source_real_coordinate_rational, source_real_coordinate_rational,
    QuadraticModel.CM.cm_quadratic_map_apply, map_add, map_mul, hδc]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, mul_zero, add_zero]
  ring

/-- The conjugate coordinate is also retained explicitly, for the native
unitary convention with distinguished skew coefficient a negative multiple of `I`. -/
def sourceConjugateComplexCoordinate (i : Fin places.count) :
    RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
      (.inl (RealPlaces.CM.sourceRealPlaces K places i)) ≃+* ℂ :=
  (sourceComplexCoordinate K places δ hδ hδ0 i).trans Complex.conjAe.toRingEquiv

theorem source_conjugate_complex_coordinate_apply (i : Fin places.count)
    (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
      (.inl (RealPlaces.CM.sourceRealPlaces K places i))) :
    sourceConjugateComplexCoordinate K places δ hδ hδ0 i x =
      star (sourceComplexCoordinate K places δ hδ hδ0 i x) := rfl

theorem source_conjugate_complex_coordinate_continuous (i : Fin places.count) :
    Continuous (sourceConjugateComplexCoordinate K places δ hδ hδ0 i) :=
  Complex.continuous_conj.comp (source_complex_coordinate_continuous K places δ hδ hδ0 i)

theorem source_conjugate_complex_coordinate_inverse_continuous (i : Fin places.count) :
    Continuous (sourceConjugateComplexCoordinate K places δ hδ hδ0 i).symm :=
  (source_complex_coordinate_inverse_continuous K places δ hδ hδ0 i).comp Complex.continuous_conj

theorem source_conjugate_complex_coordinate_scalar (i : Fin places.count)
    (x : (RealPlaces.CM.sourceRealPlaces K places i).Completion) :
    sourceConjugateComplexCoordinate K places δ hδ hδ0 i (algebraMap _ _ x) =
      (sourceRealCoordinate K places i x : ℂ) := by
  rw [source_conjugate_complex_coordinate_apply, source_complex_coordinate_scalar]
  exact Complex.conj_ofReal _

theorem source_conjugate_complex_coordinate_star (i : Fin places.count)
    (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
      (.inl (RealPlaces.CM.sourceRealPlaces K places i))) :
    sourceConjugateComplexCoordinate K places δ hδ hδ0 i (star x) =
      star (sourceConjugateComplexCoordinate K places δ hδ hδ0 i x) :=
  congrArg star (source_complex_coordinate_star K places δ hδ hδ0 i x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMArchimedeanCoordinates.CM
