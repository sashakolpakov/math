import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectedFamilyGraphRecovery

/-! # Projected Embedding Graph Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectedEmbeddingGraphRecovery

noncomputable section

/-! The ideal family of an embedded scheme with isomorphic first projection is the actual reembedded graph of the recovered morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem projectedEmbedding_graph_recovery
    {S : Scheme.{u}} {X A B P : Over S}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom]
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    (i : X ⟶ P) [IsClosedImmersion i.left] (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left]
    (h : X ⟶ A ⊗ B) [IsIso (h ≫ fst A B)] (hh : h ≫ j = i) :
    (MorphismGraphFamilies.morphismGraphFamily (ProjectedFamilyGraphRecovery.morphismOfProductProjection h)).reembed j = Closed.Families.FlatClosedFamily.ofEmbedding i := by
  change (Closed.Families.FlatClosedFamily.ofEmbedding (MorphismGraphFamilies.familyGraph (ProjectedFamilyGraphRecovery.morphismOfProductProjection h))).reembed j = _
  rw [Closed.Families.FlatClosedFamily.ofEmbedding_reembed]
  have : IsClosedImmersion (MorphismGraphFamilies.familyGraph (ProjectedFamilyGraphRecovery.morphismOfProductProjection h) ≫ j).left :=
    inferInstanceAs (IsClosedImmersion ((MorphismGraphFamilies.familyGraph (ProjectedFamilyGraphRecovery.morphismOfProductProjection h)).left ≫ j.left))
  apply Closed.Families.FlatClosedFamily.ofEmbedding_eq_of_iso _ (Closed.Families.FlatClosedFamily.ofEmbedding i)
    ((asIso (h ≫ fst A B)).symm ≪≫ Closed.Families.FlatClosedFamily.ofEmbeddingIso i)
  change inv (h ≫ fst A B) ≫ (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).hom ≫
      (Closed.Families.FlatClosedFamily.ofEmbedding i).inclusion = MorphismGraphFamilies.familyGraph (ProjectedFamilyGraphRecovery.morphismOfProductProjection h) ≫ j
  rw [Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion, ProjectedFamilyGraphRecovery.morphismOfProductProjection_graph, Category.assoc, hh]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectedEmbeddingGraphRecovery
