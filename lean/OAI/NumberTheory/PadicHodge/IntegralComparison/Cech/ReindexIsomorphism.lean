import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Reindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexCover

/-! # Reindex Isomorphism -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ReindexIsomorphism

noncomputable section

/-! The actual inverse-image comparison transfers invertibility of
refinement maps in either direction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Reindex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem left {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : D ⟶ E) (e : A ≅ D) (f : B ≅ E)
    [IsIso b] (h : a ≫ f.hom = e.hom ≫ b) : IsIso a := by
  have ha : a = e.hom ≫ b ≫ f.inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [ha]
  infer_instance

private theorem right {C : Type*} [Category C] {A B D E : C}
    (a : A ⟶ B) (b : D ⟶ E) (e : A ≅ D) (f : B ≅ E)
    [IsIso a] (h : a ≫ f.hom = e.hom ≫ b) : IsIso b := by
  have hb : b = e.inv ≫ a ≫ f.hom := by
    rw [h, Iso.inv_hom_id_assoc]
  rw [hb]
  infer_instance

universe u v
variable {X Y : TopCat.{u}} (f : Y ⟶ X)
attribute [local instance] RelativeCech.ReindexData.preimage_limits
variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : Opens X) (V : ι → Opens X) (W : κ → Opens X)
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  (K : CochainComplex ((Opens Y)ᵒᵖ ⥤ D) ℕ) (q : ℕ)

theorem relative_pushed
    [IsIso (RelativeCech.Refinement.homology ((RelativeCech.ReindexData.preimage f).obj U)
      ((RelativeCech.ReindexData.preimage f).obj ∘ V) ((RelativeCech.ReindexData.preimage f).obj ∘ W) (RelativeCech.Reindex.mapped f V W r) K q)] :
    IsIso (RelativeCech.Refinement.homology U V W r (RelativeCech.ReindexTotal.pushed f K) q) :=
  left _ _ (homologyMapIso (RelativeCech.ReindexTotal.sourceTotalIso f U V K) q)
    (homologyMapIso (RelativeCech.ReindexTotal.sourceTotalIso f U W K) q)
    (RelativeCech.Reindex.homology_refinement f U V W r K q)

theorem relative_source
    [IsIso (RelativeCech.Refinement.homology U V W r (RelativeCech.ReindexTotal.pushed f K) q)] :
    IsIso (RelativeCech.Refinement.homology ((RelativeCech.ReindexData.preimage f).obj U)
      ((RelativeCech.ReindexData.preimage f).obj ∘ V) ((RelativeCech.ReindexData.preimage f).obj ∘ W) (RelativeCech.Reindex.mapped f V W r) K q) :=
  right _ _ (homologyMapIso (RelativeCech.ReindexTotal.sourceTotalIso f U V K) q)
    (homologyMapIso (RelativeCech.ReindexTotal.sourceTotalIso f U W K) q)
    (RelativeCech.Reindex.homology_refinement f U V W r K q)

theorem ordered_pushed
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap ((RelativeCech.ReindexData.preimage f).obj ∘ V)
      ((RelativeCech.ReindexData.preimage f).obj ∘ W) (RelativeCech.Reindex.mapped f V W r) K) q)] :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap V W r (RelativeCech.ReindexTotal.pushed f K)) q) :=
  left _ _ (homologyMapIso (OrderedCech.ReindexTotal.totalIso (RelativeCech.ReindexData.preimage f) V K) q)
    (homologyMapIso (OrderedCech.ReindexTotal.totalIso (RelativeCech.ReindexData.preimage f) W K) q)
    (OrderedCech.ReindexCover.Total.homology_refinement (RelativeCech.ReindexData.preimage f) V W r K q)

theorem ordered_source
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V W r (RelativeCech.ReindexTotal.pushed f K)) q)] :
    IsIso (homologyMap (OrderedCech.Refinement.totalMap ((RelativeCech.ReindexData.preimage f).obj ∘ V)
      ((RelativeCech.ReindexData.preimage f).obj ∘ W) (RelativeCech.Reindex.mapped f V W r) K) q) :=
  right _ _ (homologyMapIso (OrderedCech.ReindexTotal.totalIso (RelativeCech.ReindexData.preimage f) V K) q)
    (homologyMapIso (OrderedCech.ReindexTotal.totalIso (RelativeCech.ReindexData.preimage f) W K) q)
    (OrderedCech.ReindexCover.Total.homology_refinement (RelativeCech.ReindexData.preimage f) V W r K q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ReindexIsomorphism
