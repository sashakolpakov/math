import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindex

/-! # Cech Reindex Top -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTop

noncomputable section

/-! Reindexing the actual ordered Čech complex preserves the
full-intersection inclusion through the canonical product isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r]
  {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → C)
  (g : ℕ) (hg : Fintype.card ι = g)

def objectIso : r.obj (CechCoordinates.topObject U g hg) ≅ CechCoordinates.topObject (r.obj ∘ U) g hg :=
  PreservesProduct.iso r (fun j : Fin g => U ((CechCoordinates.topIndex g hg).val j))

variable {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]
  (P : Dᵒᵖ ⥤ A)

def coefficient : P.obj (op (r.obj (CechCoordinates.topObject U g hg))) ⟶
    P.obj (op (CechCoordinates.topObject (r.obj ∘ U) g hg)) :=
  P.map (objectIso r U g hg).inv.op

omit [Preadditive A] in
theorem inclusion :
    CechCoordinates.topInclusion U (r.op ⋙ P) g hg ≫ (CechReindex.componentIso r U P g).hom =
      coefficient r U g hg P ≫ CechCoordinates.topInclusion (r.obj ∘ U) P g hg := by
  apply Pi.hom_ext
  intro a
  erw [Category.assoc, CechReindex.component_hom_π, ← Category.assoc,
    CechCoordinates.topInclusion_comp_pi, Category.assoc, CechCoordinates.topInclusion_comp_pi]
  change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
  exact (P.map_comp _ _).symm.trans
    ((congrArg P.map (Subsingleton.elim _ _)).trans (P.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTop
