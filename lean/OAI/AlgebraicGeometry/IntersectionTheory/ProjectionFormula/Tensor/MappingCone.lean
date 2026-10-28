import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Cochain
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Mapping Cone -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.MappingCone

noncomputable section

/-! Tensoring a mapping cone agrees with the mapping cone of the tensor map.
Both directions use the native cone inclusions and projections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CochainComplex _root_.CochainComplex.HomComplex

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.Cochain

variable (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℤ)
variable {P Q : CochainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

def hom : (Homotopy.complexFunctor R K).obj (mappingCone f) ⟶
    mappingCone ((Homotopy.complexFunctor R K).map f) :=
  mappingCone.lift _ (Tensor.Cochain.mapCocycle R K (mappingCone.fst f)) (Tensor.Cochain.map R K (mappingCone.snd f)) (by
    rw [← Tensor.Cochain.map_δ, mappingCone.δ_snd, Tensor.Cochain.map_neg, Tensor.Cochain.map_comp, Tensor.Cochain.map_ofHom]
    exact neg_add_cancel _)

def inv : mappingCone ((Homotopy.complexFunctor R K).map f) ⟶
    (Homotopy.complexFunctor R K).obj (mappingCone f) :=
  mappingCone.desc _ (Tensor.Cochain.map R K (mappingCone.inl f))
    ((Homotopy.complexFunctor R K).map (mappingCone.inr f)) (by
      rw [← Tensor.Cochain.map_δ, mappingCone.δ_inl, Tensor.Cochain.map_ofHom, CategoryTheory.Functor.map_comp])

theorem hom_ofHom : Cochain.ofHom (Tensor.MappingCone.hom R K f) =
    mappingCone.liftCochain ((Homotopy.complexFunctor R K).map f)
      (Tensor.Cochain.map R K (mappingCone.fst f).1) (Tensor.Cochain.map R K (mappingCone.snd f)) (zero_add 1) := by
  apply mappingCone.ofHom_lift

theorem inv_ofHom : Cochain.ofHom (Tensor.MappingCone.inv R K f) =
    mappingCone.descCochain ((Homotopy.complexFunctor R K).map f)
      (Tensor.Cochain.map R K (mappingCone.inl f)) (Tensor.Cochain.map R K (Cochain.ofHom (mappingCone.inr f)))
      (neg_add_cancel 1) := by
  rw [Tensor.Cochain.map_ofHom]
  apply mappingCone.ofHom_desc

theorem hom_inv_id : Tensor.MappingCone.hom R K f ≫ Tensor.MappingCone.inv R K f = 𝟙 _ := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, hom_ofHom, inv_ofHom,
    mappingCone.liftCochain_descCochain, ← Tensor.Cochain.map_comp, ← Tensor.Cochain.map_comp, ← Tensor.Cochain.map_add,
    mappingCone.id, Tensor.Cochain.map_ofHom, CategoryTheory.Functor.map_id]

theorem inv_hom_id : Tensor.MappingCone.inv R K f ≫ Tensor.MappingCone.hom R K f = 𝟙 _ := by
  apply Cochain.ofHom_injective
  rw [Cochain.ofHom_comp, inv_ofHom, hom_ofHom]
  apply (mappingCone.ext_cochain_from_iff _ (-1) 0 (neg_add_cancel 1)).2
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain,
      mappingCone.inl_descCochain, Cochain.comp_id]
    simp only [mappingCone.liftCochain, Cochain.comp_add]
    rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_neg_cancel 1) (by omega),
      ← Tensor.Cochain.map_comp, mappingCone.inl_fst, Tensor.Cochain.map_ofHom, CategoryTheory.Functor.map_id, Cochain.id_comp,
      ← Cochain.comp_assoc_of_second_is_zero_cochain,
      ← Tensor.Cochain.map_comp, mappingCone.inl_snd, Tensor.Cochain.map_zero, Cochain.zero_comp, add_zero]
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain,
      mappingCone.inr_descCochain, Cochain.comp_id]
    simp only [mappingCone.liftCochain, Cochain.comp_add]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain,
      ← Tensor.Cochain.map_comp, mappingCone.inr_fst, Tensor.Cochain.map_zero, Cochain.zero_comp, zero_add,
      ← Cochain.comp_assoc_of_second_is_zero_cochain,
      ← Tensor.Cochain.map_comp, mappingCone.inr_snd, Tensor.Cochain.map_ofHom, CategoryTheory.Functor.map_id, Cochain.id_comp]

def iso : (Homotopy.complexFunctor R K).obj (mappingCone f) ≅
    mappingCone ((Homotopy.complexFunctor R K).map f) where
  hom := Tensor.MappingCone.hom R K f
  inv := Tensor.MappingCone.inv R K f
  hom_inv_id := Tensor.MappingCone.hom_inv_id R K f
  inv_hom_id := Tensor.MappingCone.inv_hom_id R K f

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.MappingCone
