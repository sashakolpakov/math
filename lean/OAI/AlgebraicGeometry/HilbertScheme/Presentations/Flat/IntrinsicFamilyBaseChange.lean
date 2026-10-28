import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.OverCoordinateBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationBaseChangeEquality
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatPolynomialConstancy

/-! # Intrinsic Family Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.IntrinsicFamilyBaseChange.GradedHilbert

noncomputable section

/-! Native families made from homogeneous flat models recover their
exact coordinates after arbitrary base change and retain the model polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable [LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem nativeFamilyOfHomogeneousIdeal_over_pullback_coordinates
    (f : Spec (.of R) ⟶ S) (a : Spec (.of A) ⟶ S)
    (b : Over.mk a ⟶ Over.mk f)
    (hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) = b.left) :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b
      (Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal n f I)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) := by
  rw [Affine.OverCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_over_baseChange f a b (algebraMap R A) hb,
    Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal_coordinates]
  exact Projective.SaturationBaseChangeEquality.GradedHilbert.projectiveSaturation_extended_eq_of_eq (A := A) (Projective.Saturation.GradedHilbert.projectiveSaturation I) I
    (Projective.Saturation.GradedHilbert.projectiveSaturation_idempotent I)

theorem nativeFamilyOfHomogeneousIdeal_pullback_eq
    (f : Spec (.of R) ⟶ S) (a : Spec (.of A) ⟶ S)
    (b : Over.mk a ⟶ Over.mk f)
    (hb : Spec.map (CommRingCat.ofHom (algebraMap R A)) = b.left)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (hF : Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)) :
    Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b (Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal n f I) = F := by
  apply Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n a
  exact (nativeFamilyOfHomogeneousIdeal_over_pullback_coordinates I f a b hb).trans hF.symm

omit [Algebra R A] in
theorem localFlat_nativeFamily_residue_polynomial [IsNoetherianRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ S) (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (p : PrimeSpectrum R) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal n f I)))).toIdeal P := by
  rw [Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal_coordinates,
    Projective.SaturationBaseChangeEquality.GradedHilbert.projectiveSaturation_extended_eq_of_eq (A := p.asIdeal.ResidueField) (Projective.Saturation.GradedHilbert.projectiveSaturation I) I
      (Projective.Saturation.GradedHilbert.projectiveSaturation_idempotent I)]
  exact (Local.FlatPolynomialConstancy.GradedHilbert.localFlat_saturated_fiber_polynomial_iff I p.asIdeal.ResidueField P).mpr hP

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.IntrinsicFamilyBaseChange.GradedHilbert
