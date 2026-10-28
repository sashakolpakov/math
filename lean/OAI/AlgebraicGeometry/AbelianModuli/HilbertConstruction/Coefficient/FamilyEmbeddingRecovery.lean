import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.FamilyEmbeddingIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.DiagramComparison

/-! # Family Embedding Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual coefficient recovery is Cartesian for the prescribed projective embeddings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}
variable {F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)} (E : Single.DegreeFamilyModels.ProjectiveFamilyEquations F)
variable (B : Type v) [CommRing B] [Algebra B R]

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModelMap_embedding :
    E.coefficientModelMap B ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (E.modelIdeal B) =
      F.inclusion.left ≫ Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := E.coefficientRing B) (A := R) (n := n) := by
  let d : F.scheme.left ⟶ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B)) :=
    (E.coefficientModelIso B).inv.left
  let p : HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B)) ⟶
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient (E.modelIdeal B) := HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := R) (E.modelIdeal B)
  let j : HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B)) ⟶
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).left := HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion _
  let j₀ : HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient (E.modelIdeal B) ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace (E.coefficientRing B) n).left :=
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion _
  let p₀ : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace (E.coefficientRing B) n).left :=
    Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := E.coefficientRing B) (A := R) (n := n)
  have hi : d ≫ j = F.inclusion.left := congrArg (fun f => f.left) (E.coefficientModelIso_inv_embedding B)
  have hp : p ≫ j₀ = j ≫ p₀ := (Polynomial.ProjectiveCoefficients.projectiveQuotientInclusion_coefficient (E.modelIdeal B)).symm
  change (d ≫ p) ≫ j₀ = F.inclusion.left ≫ p₀
  rw [Category.assoc, hp, ← Category.assoc, hi]

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModelEmbedding_isPullback :
    IsPullback (E.coefficientModelMap B) F.inclusion.left
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (E.modelIdeal B))
      (Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := E.coefficientRing B) (A := R) (n := n)) :=
  Cartesian.DiagramComparison.isPullback_arrow_of_base_squares _ _ F.scheme.hom (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom
    (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (E.modelIdeal B))) (Projective.ProjectivePresentations.affineProjectiveSpace (E.coefficientRing B) n).hom
    (Spec.map (CommRingCat.ofHom (E.coefficientRing B).val.toRingHom)) _ _
    (E.coefficientModel_isPullback B) Projective.CoefficientPullback.polynomialProjectiveCoefficient_isPullback
    F.inclusion.w (Projective.CoefficientPullback.projectiveQuotientInclusion_standard_over (E.modelIdeal B)) (E.coefficientModelMap_embedding B)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
