import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Coproduct Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.CoproductIso

noncomputable section

/-! Additive contravariant functors preserve finite direct sums, with
the maps given by the actual inclusions and projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type w} [Category.{z} D] [Preadditive D] [HasFiniteBiproducts D]
  (F : Cᵒᵖ ⥤ D) [F.Additive] {I : Type} [Fintype I] (M : I → C)

open scoped Classical in
def biproductIso : F.obj (op (⨁ M)) ≅ ⨁ (fun i => F.obj (op (M i))) where
  hom := biproduct.lift (fun i => F.map (biproduct.ι M i).op)
  inv := biproduct.desc (fun i => F.map (biproduct.π M i).op)
  hom_inv_id := by
    rw [biproduct.lift_desc]
    simp only [← F.map_comp, ← F.map_sum, ← op_comp, ← op_sum,
      biproduct.total, op_id, F.map_id]
  inv_hom_id := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.comp_id, ← Category.assoc, biproduct.ι_desc]
    rw [Category.assoc, biproduct.lift_π, ← F.map_comp, ← op_comp]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]

def coproductIso : F.obj (op (∐ M)) ≅ ∐ (fun i => F.obj (op (M i))) :=
  F.mapIso (biproduct.isoCoproduct M).op ≪≫ biproductIso F M ≪≫
    biproduct.isoCoproduct (fun i => F.obj (op (M i)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.CoproductIso
