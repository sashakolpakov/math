import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicPolynomialFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence

/-! # Intrinsic Homogeneous Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert

noncomputable section

/-! Every native projective family on an affine test has canonical saturated
homogeneous coordinates, with the same actual closed subscheme and family properties. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem homogeneousIdealOfSheaf_projection_property
    (I : (Proj (Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (hQ : Q (I.subschemeι ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))) :
    Q (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I))) := by
  let J := ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I
  let j : Projective.Quotient.GradedHilbert.projectiveQuotient J ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J
  let p : Proj (Hilbert.Polynomial.GradedHilbert.grading R n) ⟶ Spec (CommRingCat.of R) := Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n)
  let pJ : Projective.Quotient.GradedHilbert.projectiveQuotient J ⟶ Spec (CommRingCat.of R) := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)
  have he : j.toImage ≫ (j.ker.subschemeι ≫ p) = pJ := by
    change j.toImage ≫ (j.imageι ≫ p) = pJ
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ p) j.toImage_imageι).trans (Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure J))
  change Q pJ
  rw [← he, Q.cancel_left_of_respectsIso]
  change Q ((Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf I)).ker.subschemeι ≫ p)
  rw [Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf]
  exact hQ

variable {S : Scheme.{u}} (n : ℕ) (a : Spec (CommRingCat.of R) ⟶ S)
variable (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))

def affineNativeHomogeneousIdeal : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n a F).ideal

theorem affineNativeHomogeneousIdeal_saturated : Hilbert.Polynomial.GradedHilbert.IsSaturated (affineNativeHomogeneousIdeal n a F).toIdeal :=
  ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_saturated _

theorem affineNativeHomogeneousIdeal_kernel :
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (affineNativeHomogeneousIdeal n a F)).ker =
      F.val.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom :=
  Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf _

theorem affineNativeHomogeneousIdeal_flat :
    Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (affineNativeHomogeneousIdeal n a F))) := by
  have : MorphismProperty.RespectsIso @Flat.{u} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstanceAs (Flat f))
  exact homogeneousIdealOfSheaf_projection_property _ (@Flat) (IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n a F).flat

theorem affineNativeHomogeneousIdeal_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (affineNativeHomogeneousIdeal n a F))) := by
  have : MorphismProperty.RespectsIso @LocallyOfFinitePresentation.{u} :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstanceAs (LocallyOfFinitePresentation f))
  exact homogeneousIdealOfSheaf_projection_property _ (@LocallyOfFinitePresentation)
    (IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n a F).locallyFinitePresentation

theorem affineNativeHomogeneousIdeal_global_kernel :
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (affineNativeHomogeneousIdeal n a F) ≫ (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom).ker = F.val := by
  rw [Global.PolynomialInclusion.closedImmersion_comp_iso_ker, affineNativeHomogeneousIdeal_kernel,
    ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert
