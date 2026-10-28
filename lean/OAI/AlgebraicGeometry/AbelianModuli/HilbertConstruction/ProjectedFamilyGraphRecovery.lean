import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery

/-! # Projected Family Graph Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectedFamilyGraphRecovery

noncomputable section

/-! An embedded family factoring into a product with invertible first projection is exactly the reembedded graph of the recovered morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {X A B : Over S} (h : X ⟶ A ⊗ B) [IsIso (h ≫ fst A B)]

def morphismOfProductProjection : A ⟶ B := inv (h ≫ fst A B) ≫ h ≫ snd A B

theorem morphismOfProductProjection_graph :
    MorphismGraphFamilies.familyGraph (morphismOfProductProjection h) = inv (h ≫ fst A B) ≫ h := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [MorphismGraphFamilies.familyGraph, lift_fst, Category.assoc, IsIso.inv_hom_id]
  · simp only [MorphismGraphFamilies.familyGraph, lift_snd, morphismOfProductProjection, Category.assoc]

theorem projectedFamily_graph_recovery
    {S : Scheme.{u}} {A B P : Over S} [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [IsSeparated B.hom] (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left]
    (F : Closed.Families.FlatClosedFamily P) (h : F.scheme ⟶ A ⊗ B) [IsIso (h ≫ fst A B)]
    (hh : h ≫ j = F.inclusion) :
    (MorphismGraphFamilies.morphismGraphFamily (morphismOfProductProjection h)).reembed j = F := by
  change (Closed.Families.FlatClosedFamily.ofEmbedding (MorphismGraphFamilies.familyGraph (morphismOfProductProjection h))).reembed j = F
  rw [Closed.Families.FlatClosedFamily.ofEmbedding_reembed]
  have : IsClosedImmersion (MorphismGraphFamilies.familyGraph (morphismOfProductProjection h) ≫ j).left :=
    inferInstanceAs (IsClosedImmersion ((MorphismGraphFamilies.familyGraph (morphismOfProductProjection h)).left ≫ j.left))
  apply Closed.Families.FlatClosedFamily.ofEmbedding_eq_of_iso _ F (asIso (h ≫ fst A B)).symm
  change inv (h ≫ fst A B) ≫ F.inclusion = MorphismGraphFamilies.familyGraph (morphismOfProductProjection h) ≫ j
  rw [morphismOfProductProjection_graph, Category.assoc, hh]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectedFamilyGraphRecovery
