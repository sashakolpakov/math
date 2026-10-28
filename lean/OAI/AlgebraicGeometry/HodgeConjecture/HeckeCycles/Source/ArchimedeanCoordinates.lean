import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanPlaces
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.QuadraticCoordinates
import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational

/-! # Archimedean Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanCoordinates.CM

noncomputable section

/-! Actual complex coordinates at every source archimedean place,
including scalar, conjugation, and rational-field compatibility. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.RepresentationTheory.Weil.AdelicSplitting.Rational.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanPlaces.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

theorem delta_re (i : Fin places.count) : (ReferenceDatum.CM.embeddings E places i C.delta).re = 0 := by
  have hc := IsCMField.complexEmbedding_complexConj E (ReferenceDatum.CM.embeddings E places i).toRingHom C.delta
  change ReferenceDatum.CM.embeddings E places i (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E C.delta) =
    star (ReferenceDatum.CM.embeddings E places i C.delta) at hc
  rw [C.delta_imaginary, map_neg] at hc
  have h := congrArg Complex.re hc
  change (-(ReferenceDatum.CM.embeddings E places i C.delta)).re = (starRingEnd ℂ (ReferenceDatum.CM.embeddings E places i C.delta)).re at h
  simp only [Complex.neg_re, Complex.conj_re] at h
  linarith

theorem delta_im_ne_zero (i : Fin places.count) : (ReferenceDatum.CM.embeddings E places i C.delta).im ≠ 0 := by
  intro h
  apply C.delta_ne_zero
  apply (ReferenceDatum.CM.embeddings E places i).injective
  rw [map_zero]
  exact Complex.ext (delta_re E C i) h

theorem discriminant_real (i : Fin places.count) :
    ArchimedeanPlaces.CM.realCoordinate E places i
      (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E) (.inl (ArchimedeanPlaces.CM.enumeration E places i)) (QuadraticConjugation.CM.Field.discriminant E C)) =
        -((ReferenceDatum.CM.embeddings E places i C.delta).im ^ 2) := by
  have h := congrArg Complex.re (ArchimedeanPlaces.CM.rational E places i (QuadraticConjugation.CM.Field.discriminant E C))
  change _ = (ReferenceDatum.CM.embeddings E places i (C.delta ^ 2)).re at h
  rw [map_pow] at h
  simpa only [Complex.ofReal_re, pow_two, Complex.mul_re,
    delta_re E C i, zero_mul, zero_sub] using h

def complexCoordinate (i : Fin places.count) :
    RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (.inl (ArchimedeanPlaces.CM.enumeration E places i)) ≃+* ℂ :=
  Real.QuadraticCoordinates.CM.equivalence (ArchimedeanPlaces.CM.realCoordinate E places i) _
    (ReferenceDatum.CM.embeddings E places i C.delta).im (discriminant_real E C i) (delta_im_ne_zero E C i)

theorem continuous (i : Fin places.count) : Continuous (complexCoordinate E C i) :=
  Real.QuadraticCoordinates.CM.continuous _ _ _ _ _ (ArchimedeanPlaces.CM.real_continuous E places i)

theorem inverse_continuous (i : Fin places.count) : Continuous (complexCoordinate E C i).symm :=
  Real.QuadraticCoordinates.CM.inverse_continuous _ _ _ _ _ (ArchimedeanPlaces.CM.real_inverse_continuous E places i)

theorem scalar (i : Fin places.count) (x : (ArchimedeanPlaces.CM.enumeration E places i).Completion) :
    complexCoordinate E C i (algebraMap _ _ x) = (ArchimedeanPlaces.CM.realCoordinate E places i x : ℂ) :=
  Real.QuadraticCoordinates.CM.scalar _ _ _ _ _ x

theorem star (i : Fin places.count)
    (x : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (.inl (ArchimedeanPlaces.CM.enumeration E places i))) :
    complexCoordinate E C i (star x) = star (complexCoordinate E C i x) :=
  Real.QuadraticCoordinates.CM.star _ _ _ _ _ x

theorem rational_compatibility (i : Fin places.count)
    (x : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C)) :
    complexCoordinate E C i
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (QuadraticConjugation.CM.Field.RealField E) (QuadraticConjugation.CM.Field.discriminant E C) (.inl (ArchimedeanPlaces.CM.enumeration E places i)) x) =
        ReferenceDatum.CM.embeddings E places i (QuadraticConjugation.CM.Field.fieldEquiv E C x) := by
  have hδ : ReferenceDatum.CM.embeddings E places i C.delta = ((ReferenceDatum.CM.embeddings E places i C.delta).im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using delta_re E C i
    · simp
  change (ArchimedeanPlaces.CM.realCoordinate E places i (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E)
    (.inl (ArchimedeanPlaces.CM.enumeration E places i)) x.re) : ℂ) +
    (ArchimedeanPlaces.CM.realCoordinate E places i (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (QuadraticConjugation.CM.Field.RealField E)
      (.inl (ArchimedeanPlaces.CM.enumeration E places i)) x.im) : ℂ) *
      ((ReferenceDatum.CM.embeddings E places i C.delta).im : ℂ) * Complex.I =
        ReferenceDatum.CM.embeddings E places i (QuadraticConjugation.CM.Field.toOriginal E C x)
  rw [ArchimedeanPlaces.CM.rational, ArchimedeanPlaces.CM.rational, QuadraticConjugation.CM.Field.toOriginal_apply, map_add, map_mul, hδ]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
    Complex.I_re, mul_one, mul_zero, add_zero]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ArchimedeanCoordinates.CM
