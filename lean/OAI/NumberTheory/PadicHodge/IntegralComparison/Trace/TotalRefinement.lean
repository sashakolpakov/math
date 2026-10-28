import OAI.NumberTheory.PadicHodge.IntegralComparison.SerreUnitTrace

/-! # Total Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.TotalRefinement

noncomputable section

/-! A trace-preserving map of actual total complexes descends through
an isomorphic refinement. The resulting normalized class is represented
by that map, before any concentration or purity comparison. -/

open _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R]
  {A B C : AddCommGrpCat.{u}}
  (tA : A ≅ AddCommGrpCat.of R) (tB : B ≅ AddCommGrpCat.of R)
  (tC : C ≅ AddCommGrpCat.of R)
  (a : A ⟶ C) (b : B ⟶ C)
  (ha : a ≫ tC.hom = tA.hom) (hb : b ≫ tC.hom = tB.hom)

include ha in
theorem left_isIso : IsIso a := by
  have h : a = tA.hom ≫ tC.inv := by
    rw [← ha, Category.assoc, tC.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

def map : B ⟶ A := by
  letI := left_isIso tA tC a ha
  exact b ≫ (asIso a).inv

include hb in
@[reassoc]
theorem map_trace : map tA tC a b ha ≫ tA.hom = tB.hom := by
  let := left_isIso tA tC a ha
  change b ≫ inv a ≫ tA.hom = _
  rw [← ha, IsIso.inv_hom_id_assoc]
  exact hb

def unitClass : A := map tA tC a b ha (tB.inv (1 : R))

include hb in
theorem unitClass_trace : tA.hom (unitClass tA tB tC a b ha) = 1 := by
  have h := ConcreteCategory.congr_hom (map_trace tA tB tC a b ha hb) (tB.inv (1 : R))
  exact h.trans (Iso.inv_hom_id_apply tB (1 : R))

include hb in
theorem unitClass_eq : unitClass tA tB tC a b ha = tA.inv (1 : R) := by
  apply (ConcreteCategory.bijective_of_isIso tA.hom).injective
  rw [unitClass_trace tA tB tC a b ha hb, Iso.inv_hom_id_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.TotalRefinement
