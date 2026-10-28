import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.FamilyBaseChange

/-! # Embedding Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-! Generated finite-data families preserve their actual projective embeddings under base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem EmbeddingBaseChange.homogeneousProjectiveEmbedding_eqToIso {R : Type u} [CommRing R] {n : ℕ}
    {I J : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)} (h : I = J) :
    (eqToIso (congrArg Projective.EmbeddingBaseChange.homogeneousProjectiveFamily h)).hom ≫ Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding J =
      Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I := by
  subst J
  exact Category.id_comp _

variable {R : Type u} [CommRing R] {n B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r)
variable (A : Type u) [CommRing A] [Algebra R A]

theorem GradedClassification.TruncatedGradedQuotientData.projectiveEmbedding_baseChange :
    (D.projectiveFamilyBaseChangeIso A).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map D.projectiveEmbedding =
        (D.baseChange A).projectiveEmbedding ≫
          (Projective.SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := R) (A := A) n).hom := by
  change ((eqToIso (congrArg Projective.EmbeddingBaseChange.homogeneousProjectiveFamily
      (D.baseChange_generatedIdeal A))).hom ≫
      (Projective.EmbeddingBaseChange.homogeneousProjectiveBaseChangeIso (A := A) D.generatedIdeal).hom) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
          (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding D.generatedIdeal) =
    Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (D.baseChange A).generatedIdeal ≫
      (Projective.SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := R) (A := A) n).hom
  rw [Category.assoc, Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding_baseChange, ← Category.assoc]
  exact congrArg (fun j => j ≫ (Projective.SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := R) (A := A) n).hom)
    (EmbeddingBaseChange.homogeneousProjectiveEmbedding_eqToIso (D.baseChange_generatedIdeal A))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
