import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex

/-! # Reindex Composition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexComposition

noncomputable section

/-! Ordered inverse-image coordinates compose through the original
chosen finite products. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
private theorem components {A : Type v} [Category A] {ι : Type u} [HasProducts.{u} A]
    {L M N : ι → A} (e : ∀ i, L i ≅ M i) (f : ∀ i, M i ≅ N i) (g : ∀ i, L i ≅ N i)
    (h : ∀ i, (e i).hom ≫ (f i).hom = (g i).hom) :
    (Pi.mapIso e).hom ≫ (Pi.mapIso f).hom = (Pi.mapIso g).hom := by
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.mapIso_hom_π, Pi.mapIso_hom_π_assoc, h]

variable {C D E : Type u}
  [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  [Preorder E] [HasFiniteProducts E]
  (r : C ⥤ D) [PreservesFiniteLimits r] (s : D ⥤ E) [PreservesFiniteLimits s]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] (P : Eᵒᵖ ⥤ A)

theorem composition :
    (Reindex.iso r U (s.op ⋙ P)).hom ≫
      (Reindex.iso s (r.obj ∘ U) P).hom =
    (Reindex.iso (r ⋙ s) U P).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (AugmentedOrdered.CechReindex.componentIso r U (s.op ⋙ P) (n+1)).hom ≫
      (AugmentedOrdered.CechReindex.componentIso s (r.obj ∘ U) P (n+1)).hom =
    (AugmentedOrdered.CechReindex.componentIso (r ⋙ s) U P (n+1)).hom
  dsimp only [AugmentedOrdered.CechReindex.componentIso]
  apply components
  intro a
  change P.map _ ≫ P.map _ = P.map _
  rw [← P.map_comp]
  congr 1

theorem inverse_composition :
    (Reindex.iso r U (s.op ⋙ P)).inv ≫
      (Reindex.iso (r ⋙ s) U P).hom =
    (Reindex.iso s (r.obj ∘ U) P).hom := by
  rw [← composition, Iso.inv_hom_id_assoc]

theorem homology (n : ℕ) :
    homologyMap (Reindex.iso r U (s.op ⋙ P)).inv n ≫
      homologyMap (Reindex.iso (r ⋙ s) U P).hom n =
    homologyMap (Reindex.iso s (r.obj ∘ U) P).hom n := by
  simpa only [homologyMap_comp] using
    congrArg (fun a => homologyMap a n) (inverse_composition r s U P)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexComposition
