import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialPartition
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.FieldBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves

/-! # Flat Closed Projective Polynomials -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatClosedProjectivePolynomials

noncomputable section

/-! The clopen fiber-polynomial partition applies to actual closed
projective embeddings, and computes their cartesian field fibers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert
universe u
variable {R : Type u} [CommRing R] {n : ℕ} {X : Scheme.{u}}
    (f : X ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left) [IsClosedImmersion f]

theorem closedProjective_homogeneousIdeal_flat
    [Flat (f ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))] :
    Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker))) := by
  let J := f.ker
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)
  have he : HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert.projectiveIdealSheafStructure J = inv f.toImage ≫ (f ≫ p) := by
    change f.imageι ≫ p = inv f.toImage ≫ (f ≫ p)
    have hi : f.imageι = inv f.toImage ≫ f :=
      ((Iso.inv_comp_eq (asIso f.toImage)).mpr f.toImage_imageι.symm).symm
    exact (congrArg (fun h : f.image ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n).left => h ≫ p) hi).trans
      (Category.assoc _ _ _)
  have : Flat (HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert.projectiveIdealSheafStructure J) := by
    rw [he]
    infer_instance
  have h : Flat ((HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert.projectiveIdealSheafIso J).hom ≫ HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert.projectiveIdealSheafStructure J) := inferInstance
  rw [HilbertScheme.Presentations.Flat.ProjectiveIdealSheaves.GradedHilbert.projectiveIdealSheafIso_hom_structure] at h
  exact h

variable [IsNoetherianRing R]
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker)))]

theorem closedProjectiveFiber_hilbertPolynomial_iff
    {K : Type u} [Field K] (φ : R →+* K) {Y : Scheme.{u}}
    (e : Y ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left) (a : Y ⟶ X)
    (H : IsPullback a e f (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n))
    (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker).toIdeal P ↔
      FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker)
        ((IsLocalRing.closedPoint K).comap φ) = P := by
  have hker := AbelianModuli.HilbertConstruction.Projective.IdealBaseChange.closedImmersion_kernel_isPullback f e a _ H
  have h₁ := congrArg (fun J : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left.IdealSheafData =>
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J).toIdeal P) hker
  have h₂ := congrArg (fun J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n) => HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P)
    (Projective.FieldBaseChange.PolarizationEmbedding.projectiveIdeal_coefficientBaseChange (R := CommRingCat.of R)
      (A := CommRingCat.of K) (n := n) f.ker (CommRingCat.ofHom φ))
  exact (Iff.of_eq h₁).trans ((Iff.of_eq h₂).trans
    ((FlatFiberPolynomialSpecialization.PolarizationEmbedding.saturated_field_hilbertPolynomial_iff_residue (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker) φ P).trans
      (FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial_eq_iff (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker) _ P).symm))

theorem closedProjectiveFiber_has_residueHilbertPolynomial
    {K : Type u} [Field K] (φ : R →+* K) {Y : Scheme.{u}}
    (e : Y ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K n).left) (a : Y ⟶ X)
    (H : IsPullback a e f (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom φ) n)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf e.ker).toIdeal
      (FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker)
        ((IsLocalRing.closedPoint K).comap φ)) :=
  (closedProjectiveFiber_hilbertPolynomial_iff f φ e a H _).mpr rfl

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatClosedProjectivePolynomials
