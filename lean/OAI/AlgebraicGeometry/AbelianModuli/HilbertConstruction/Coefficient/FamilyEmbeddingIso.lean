import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.CoefficientModels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.EmbeddingBaseChange

/-! # Family Embedding Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The homogeneous coefficient model recovers the actual given projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {R : Type u} [CommRing R] {n : ℕ}
variable {F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n)} (E : Single.DegreeFamilyModels.ProjectiveFamilyEquations F)
variable (B : Type v) [CommRing B] [Algebra B R]

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModelIso_embedding :
    (E.coefficientModelIso B).hom ≫ F.inclusion =
      Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B)) := by
  change ((eqToIso (congrArg Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (E.modelIdeal_extension B))).hom ≫
    E.familyIso.hom) ≫ F.inclusion = _
  rw [Category.assoc, E.familyIso_embedding]
  exact Truncated.EmbeddingBaseChange.homogeneousProjectiveEmbedding_eqToIso (E.modelIdeal_extension B)

theorem Single.DegreeFamilyModels.ProjectiveFamilyEquations.coefficientModelIso_inv_embedding :
    (E.coefficientModelIso B).inv ≫
        Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (E.modelIdeal B)) = F.inclusion := by
  rw [← E.coefficientModelIso_embedding B, Iso.inv_hom_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
