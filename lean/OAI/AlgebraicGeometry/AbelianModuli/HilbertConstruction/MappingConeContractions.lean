import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Mapping Cone Contractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeContractions

noncomputable section

/-! Actual mapping-cone contractions and transport of contracting homotopies. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Pretriangulated
universe u v

section Cone
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
open _root_.CochainComplex

def mappingConeIsoOfIso {K L : CochainComplex C ℤ} (f : K ⟶ L) [IsIso f] :
    mappingCone f ≅ mappingCone (𝟙 K) where
  hom := mappingCone.map f (𝟙 K) (𝟙 K) (inv f) (by simp)
  inv := mappingCone.map (𝟙 K) f (𝟙 K) f (by simp)
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Category.id_comp, IsIso.inv_hom_id]
    exact mappingCone.map_id f
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Category.id_comp, IsIso.hom_inv_id]
    exact mappingCone.map_id (𝟙 K)

def mappingConeHomotopyToZeroOfIso {K L : CochainComplex C ℤ} (f : K ⟶ L) [IsIso f] :
    Homotopy (𝟙 (mappingCone f)) 0 := by
  let e := mappingConeIsoOfIso f
  have h := ((mappingCone.homotopyToZeroOfId K).compLeft e.hom).compRight e.inv
  simpa only [Category.id_comp, Category.comp_id, Iso.hom_inv_id, comp_zero, zero_comp] using h

theorem mappingCone_contractible_of_contractible [HasZeroObject C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : Nonempty (Homotopy (𝟙 K) 0)) (hL : Nonempty (Homotopy (𝟙 L) 0)) :
    Nonempty (Homotopy (𝟙 (mappingCone f)) 0) := by
  apply (HomotopyCategory.isZero_quotient_obj_iff _).mp
  exact (mappingCone.triangleh f).isZero₃_of_isZero₁₂
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
    ((HomotopyCategory.isZero_quotient_obj_iff K).mpr hK)
    ((HomotopyCategory.isZero_quotient_obj_iff L).mpr hL)
end Cone

theorem cochainContractible_of_iso {C : Type u} [Category.{v} C] [Preadditive C]
    {K L : CochainComplex C ℤ} (e : K ≅ L) (hL : Nonempty (Homotopy (𝟙 L) 0)) :
    Nonempty (Homotopy (𝟙 K) 0) := by
  obtain ⟨h⟩ := hL
  refine ⟨?_⟩
  simpa only [Category.id_comp, Category.comp_id, Iso.hom_inv_id, comp_zero, zero_comp]
    using (h.compLeft e.hom).compRight e.inv

theorem cochainContractible_map {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (hK : Nonempty (Homotopy (𝟙 K) 0)) :
    Nonempty (Homotopy (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj K)) 0) := by
  obtain ⟨h⟩ := hK
  exact ⟨by simpa only [CategoryTheory.Functor.map_id, Functor.map_zero] using F.mapHomotopy h⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeContractions
