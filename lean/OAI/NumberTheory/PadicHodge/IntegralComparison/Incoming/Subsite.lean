import OAI.NumberTheory.PadicHodge.IntegralComparison.SiteLifts

/-! # Subsite -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Subsite

noncomputable section

/-!
# IntegralComparison: the restricted topology on a full subcategory closed under incoming maps

Such an inclusion lifts every incoming arrow. Its native restricted
topology gives both continuous and cocontinuous restriction, and agrees
with the native induced topology.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] (P : ObjectProperty C)
  (hP : ∀ {X Y : C}, (X ⟶ Y) → P Y → P X)

def incomingLifts : SiteLifts.IncomingLifts P.ι where
  object {U V} α := ⟨V, hP α U.property⟩
  iso _ := Iso.refl _
  hom α := ObjectProperty.homMk α
  map_hom α := (Category.id_comp α).symm
  fullTriangle _ _ c h := ⟨ObjectProperty.homMk c, rfl, by
    apply P.ι.map_injective
    exact h⟩

include hP in
theorem pushforward_pullback {U : P.FullSubcategory} (S : Sieve U.obj) :
    (S.functorPullback P.ι).functorPushforward P.ι = S := by
  refine le_antisymm (Sieve.functorPullback_pushforward_le _ _) ?_
  intro V α hα
  exact ⟨⟨V, hP α U.property⟩, ObjectProperty.homMk α, 𝟙 V, hα, (Category.id_comp α).symm⟩

theorem topology_generated (J : GrothendieckTopology C) : J.toPrecoverage.toGrothendieck = J := by
  apply le_antisymm (J.toGrothendieck_toPrecoverage_le)
  intro U S hS
  rw [← Sieve.generate_sieve S]
  apply Precoverage.generate_mem_toGrothendieck
  simpa only [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_sieve] using hS

variable (J : GrothendieckTopology C)

include hP in
theorem continuous : P.ι.IsContinuous (P.ι.restrictedTopology J) J := by
  have h := (incomingLifts P hP).continuous (J.toPrecoverage.comap P.ι) J.toPrecoverage le_rfl
  rw [topology_generated] at h
  exact h

include hP in
theorem cocontinuous : P.ι.IsCocontinuous (P.ι.restrictedTopology J) J where
  cover_lift {U S} hS := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    rw [pushforward_pullback P hP]
    exact hS

include hP in
theorem topology_eq_induced : P.ι.restrictedTopology J = P.ι.inducedTopology J := by
  have := Subsite.continuous P hP J
  exact P.ι.restrictedTopology_eq_inducedTopology

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.Subsite
