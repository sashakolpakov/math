import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-! # Product Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProductMap.ProductMapOfFactorization

noncomputable section

/-! An open-type subobject has the same product over a test object when
the first projection factors through it. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {U V T : C} (α : U ⟶ V) [Mono α] (l : V ⨯ T ⟶ U) (hl : l ≫ α = prod.fst)

def inverse : V ⨯ T ⟶ U ⨯ T := prod.lift l prod.snd

include hl in
omit [Mono α] in
theorem inverse_hom : inverse l ≫ prod.map α (𝟙 T) = 𝟙 (V ⨯ T) := by
  dsimp only [inverse]
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, prod.lift_fst_assoc, Category.id_comp]
    exact hl
  · simp only [Category.assoc, prod.map_snd, prod.lift_snd, Category.comp_id, Category.id_comp]

include hl in
theorem hom_inverse : prod.map α (𝟙 T) ≫ inverse l = 𝟙 (U ⨯ T) := by
  dsimp only [inverse]
  apply prod.hom_ext
  · apply (cancel_mono α).mp
    simp only [Category.assoc, prod.lift_fst, hl, prod.map_fst, Category.id_comp]
  · simp only [Category.assoc, prod.lift_snd, prod.map_snd, Category.comp_id, Category.id_comp]

def iso : U ⨯ T ≅ V ⨯ T where
  hom := prod.map α (𝟙 T)
  inv := inverse l
  hom_inv_id := hom_inverse α l hl
  inv_hom_id := inverse_hom α l hl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProductMap.ProductMapOfFactorization
