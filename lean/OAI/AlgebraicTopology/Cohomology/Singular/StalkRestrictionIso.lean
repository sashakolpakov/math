import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Stalk Restriction Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso

noncomputable section

/-!
# A germ isomorphism from invertible restrictions on a neighborhood basis

For the actual filtered-colimit stalk of a module presheaf, the germ map from
a fixed neighborhood is an isomorphism whenever restriction from that
neighborhood is invertible on arbitrarily small neighborhoods of the point.
No sheaf condition or additional description of the stalk is assumed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

/-- If restrictions from a fixed neighborhood are injective on arbitrarily
small neighborhoods of a point, its actual germ map is injective. -/
theorem germ_injective_of_cofinal_restrictions
    (F : X.Presheaf (ModuleCat.{u,0} R)) (x : X) (V : Opens X) (hxV : x ∈ V)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (W : Opens X) (_hxW : x ∈ W) (hWV : W ≤ V) (_hWU : W ≤ U),
        Function.Injective (F.map (homOfLE hWV).op)) :
    Function.Injective (F.germ V x hxV) := by
  apply (injective_iff_map_eq_zero _).2
  intro s hs
  obtain ⟨U, hxU, i, hi⟩ := (StalkExactnessAt.germ_eq_zero_iff_locally_zero F x V hxV s).mp hs
  obtain ⟨W, _hxW, hWV, hWU, hinj⟩ := hlocal U hxU
  apply hinj
  rw [map_zero]
  calc
    F.map (homOfLE hWV).op s =
        F.map (homOfLE hWU).op (F.map i.op s) := by
      have hcomp : i.op ≫ (homOfLE hWU).op = (homOfLE hWV).op :=
        Subsingleton.elim _ _
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, hcomp]
    _ = 0 := by rw [hi, map_zero]

/-- If restrictions from a fixed neighborhood are surjective on arbitrarily
small neighborhoods of a point, every actual germ has a representative on it. -/
theorem germ_surjective_of_cofinal_restrictions
    (F : X.Presheaf (ModuleCat.{u,0} R)) (x : X) (V : Opens X) (hxV : x ∈ V)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (W : Opens X) (_hxW : x ∈ W) (hWV : W ≤ V) (_hWU : W ≤ U),
        Function.Surjective (F.map (homOfLE hWV).op)) :
    Function.Surjective (F.germ V x hxV) := by
  intro z
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq z
  obtain ⟨W, hxW, hWV, hWU, hsurj⟩ := hlocal U hxU
  obtain ⟨t, ht⟩ := hsurj (F.map (homOfLE hWU).op s)
  refine ⟨t, ?_⟩
  calc
    F.germ V x hxV t = F.germ W x hxW (F.map (homOfLE hWV).op t) :=
      (F.germ_res_apply (homOfLE hWV) x hxW t).symm
    _ = F.germ W x hxW (F.map (homOfLE hWU).op s) :=
      congrArg (F.germ W x hxW) ht
    _ = F.germ U x hxU s := F.germ_res_apply (homOfLE hWU) x hxW s

/-- The actual germ map is an isomorphism if restriction from its fixed
neighborhood is an isomorphism on arbitrarily small neighborhoods of the point. -/
theorem germ_isIso_of_cofinal_restrictions
    (F : X.Presheaf (ModuleCat.{u,0} R)) (x : X) (V : Opens X) (hxV : x ∈ V)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (W : Opens X) (_hxW : x ∈ W) (hWV : W ≤ V) (_hWU : W ≤ U),
        IsIso (F.map (homOfLE hWV).op)) :
    IsIso (F.germ V x hxV) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply germ_injective_of_cofinal_restrictions F x V hxV
    intro U hxU
    obtain ⟨W, hxW, hWV, hWU, h⟩ := hlocal U hxU
    let := h
    exact ⟨W, hxW, hWV, hWU,
      (ConcreteCategory.bijective_of_isIso (F.map (homOfLE hWV).op)).1⟩
  · apply germ_surjective_of_cofinal_restrictions F x V hxV
    intro U hxU
    obtain ⟨W, hxW, hWV, hWU, h⟩ := hlocal U hxU
    let := h
    exact ⟨W, hxW, hWV, hWU,
      (ConcreteCategory.bijective_of_isIso (F.map (homOfLE hWV).op)).2⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.StalkRestrictionIso
