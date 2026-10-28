import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Homogeneous Family Construction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction.GradedHilbert

noncomputable section

/-! Convert an actual flat finitely presented homogeneous projective
quotient to a native Hilbert family, with its exact canonical ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {R : Type u} [CommRing R] (n : ℕ)
variable (a : Spec (CommRingCat.of R) ⟶ S)

theorem affineNativeHomogeneousIdeal_injective : Function.Injective (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a) := by
  intro F G h
  apply Subtype.ext
  rw [← Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_global_kernel n a F,
    ← Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_global_kernel n a G, h]

variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable [LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

def nativeFamilyOfHomogeneousIdeal : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) := by
  let j : Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) ⟶ Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)) :=
    Over.homMk (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) (Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure I)
  have : IsClosedImmersion j.left := inferInstanceAs (IsClosedImmersion (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I))
  have : Flat (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))).hom :=
    inferInstanceAs (Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)))
  have : LocallyOfFinitePresentation (Over.mk (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)))
  exact Affine.IntrinsicPolynomialFamily.GradedHilbert.affinePolynomialToNative n a (AbelianModuli.HilbertConstruction.Closed.Families.FlatClosedFamily.ofEmbedding j)

theorem nativeFamilyOfHomogeneousIdeal_val :
    (nativeFamilyOfHomogeneousIdeal n a I).val =
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I).ker.comap (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).inv :=
  Affine.IntrinsicPolynomialFamily.GradedHilbert.affinePolynomialToNative_ideal n a _

theorem nativeFamilyOfHomogeneousIdeal_coordinates :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a (nativeFamilyOfHomogeneousIdeal n a I) = Projective.Saturation.GradedHilbert.projectiveSaturation I := by
  change ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
    ((nativeFamilyOfHomogeneousIdeal n a I).val.comap (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom) = _
  rw [nativeFamilyOfHomogeneousIdeal_val, ← Scheme.IdealSheafData.comap_comp,
    Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction.GradedHilbert
