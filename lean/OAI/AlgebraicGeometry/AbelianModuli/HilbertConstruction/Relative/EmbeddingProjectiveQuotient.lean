import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingIntrinsic
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.HomogeneousCoordinates

/-! # Embedding Projective Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingProjectiveQuotient

noncomputable section

/-! An actual relative projective embedding over a field gives an actual projective-quotient model. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem relativeEmbedding_has_projectiveQuotient_iso
    {K : Type u} [Field K] {n : ℕ} {A : Over (Spec (.of K))}
    (i : A ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of K)) n)
    [IsClosedImmersion i.left] [Flat A.hom] [LocallyOfFinitePresentation A.hom] :
    ∃ I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K n), Nonempty (A.left ≅ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) := by
  let F := Closed.Families.FlatClosedFamily.ofEmbedding i
  let G := F.affineProjectivePullback (𝟙 _)
  let e : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily G.homogeneousIdeal ≅ A :=
    G.homogeneousFamilyIso ≪≫ F.identityAffineFamilyIso ≪≫
      (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).symm
  exact ⟨G.homogeneousIdeal, ⟨(Over.forget _).mapIso e.symm⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingProjectiveQuotient
