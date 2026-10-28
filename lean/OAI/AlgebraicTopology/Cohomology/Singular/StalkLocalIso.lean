import OAI.AlgebraicTopology.Cohomology.Singular.StalkExactnessAt
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Stalk Local Iso -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso

noncomputable section

/-!
# Isomorphisms on a neighborhood basis induce stalk isomorphisms

These statements concern the actual filtered-colimit stalk of a module
presheaf. They require componentwise injectivity or surjectivity only on an
arbitrarily small open neighborhood of the point. No sheaf condition is needed.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.TopCat.Presheaf

universe u

variable {R : Type} [Ring R] {X : TopCat.{u}}
variable {F G : X.Presheaf (ModuleCat.{u,0} R)}

attribute [local instance] StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Injectivity on an arbitrarily small neighborhood gives injectivity on the
stalk. The proof first shrinks until the image of a section vanishes. -/
theorem stalkMap_injective_of_locally_injective (τ : F ⟶ G) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hxV : x ∈ V) (_i : V ⟶ U),
        Function.Injective (τ.app (op V))) :
    Function.Injective ((stalkFunctor (ModuleCat.{u,0} R) x).map τ) := by
  apply (injective_iff_map_eq_zero _).2
  intro z hz
  obtain ⟨U, hxU, s, rfl⟩ := F.exists_germ_eq z
  rw [stalkFunctor_map_germ_apply] at hz
  obtain ⟨V, hxV, i, hi⟩ :=
    (StalkExactnessAt.germ_eq_zero_iff_locally_zero G x U hxU (τ.app (op U) s)).mp hz
  obtain ⟨W, hxW, j, hinj⟩ := hlocal V hxV
  have hV : τ.app (op V) (F.map i.op s) = 0 :=
    (ConcreteCategory.congr_hom (τ.naturality i.op) s).trans hi
  have hW : τ.app (op W) (F.map j.op (F.map i.op s)) = 0 := by
    rw [← ConcreteCategory.comp_apply, τ.naturality, ConcreteCategory.comp_apply,
      hV, map_zero]
  have hs : F.map j.op (F.map i.op s) = 0 := hinj (by simpa only [map_zero] using hW)
  calc
    F.germ U x hxU s = F.germ V x hxV (F.map i.op s) :=
      (F.germ_res_apply i x hxV s).symm
    _ = F.germ W x hxW (F.map j.op (F.map i.op s)) :=
      (F.germ_res_apply j x hxW _).symm
    _ = 0 := by rw [hs, map_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity on an arbitrarily small neighborhood gives surjectivity on
the stalk, by lifting a restricted representative of each germ. -/
theorem stalkMap_surjective_of_locally_surjective (τ : F ⟶ G) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hxV : x ∈ V) (_i : V ⟶ U),
        Function.Surjective (τ.app (op V))) :
    Function.Surjective ((stalkFunctor (ModuleCat.{u,0} R) x).map τ) := by
  intro z
  obtain ⟨U, hxU, s, rfl⟩ := G.exists_germ_eq z
  obtain ⟨V, hxV, i, hsurj⟩ := hlocal U hxU
  obtain ⟨t, ht⟩ := hsurj (G.map i.op s)
  refine ⟨F.germ V x hxV t, ?_⟩
  rw [stalkFunctor_map_germ_apply, ht]
  exact G.germ_res_apply i x hxV s

/-- A natural transformation which is an isomorphism on arbitrarily small
neighborhoods of a point induces an isomorphism on the actual stalk there. -/
theorem stalkMap_isIso_of_locally_isIso (τ : F ⟶ G) (x : X)
    (hlocal : ∀ (U : Opens X) (_hxU : x ∈ U),
      ∃ (V : Opens X) (_hxV : x ∈ V) (_i : V ⟶ U), IsIso (τ.app (op V))) :
    IsIso ((stalkFunctor (ModuleCat.{u,0} R) x).map τ) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply stalkMap_injective_of_locally_injective τ x
    intro U hxU
    obtain ⟨V, hxV, i, h⟩ := hlocal U hxU
    let := h
    exact ⟨V, hxV, i, (ConcreteCategory.bijective_of_isIso (τ.app (op V))).1⟩
  · apply stalkMap_surjective_of_locally_surjective τ x
    intro U hxU
    obtain ⟨V, hxV, i, h⟩ := hlocal U hxU
    let := h
    exact ⟨V, hxV, i, (ConcreteCategory.bijective_of_isIso (τ.app (op V))).2⟩

end

end OAI.AlgebraicTopology.Cohomology.Singular.StalkLocalIso
