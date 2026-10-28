import Mathlib

/-! # Representable Point Topology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RepresentablePointTopology

/-! The topology in which every morphism from a fixed object belongs to each covering sieve. -/

open _root_.CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (P : C)

def topology : GrothendieckTopology C where
  sieves X := {S | ∀ f : P ⟶ X, S f}
  top_mem' _ _ := trivial
  pullback_stable' := by
    intro X Y S f h g
    exact h (g ≫ f)
  transitive' := by
    intro X S hS R hR g
    have h := hR (hS g) (𝟙 P)
    simpa only [Sieve.pullback_apply, Category.id_comp] using h

theorem covering_eq_top (J : GrothendieckTopology C) (hJ : J ≤ topology P)
    (S : Sieve P) (hS : S ∈ J P) : S = ⊤ :=
  Sieve.id_mem_iff_eq_top.mp (hJ _ hS (𝟙 P))

theorem generated_le (K : Precoverage C)
    (h : ∀ (X : C) (R : Presieve X), R ∈ K X → ∀ g : P ⟶ X,
      ∃ (Y : C) (a : Y ⟶ X), R a ∧ ∃ b : P ⟶ Y, b ≫ a = g) :
    K.toGrothendieck ≤ topology P := by
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro X R hR
  change ∀ g : P ⟶ X, Sieve.generate R g
  intro g
  obtain ⟨Y, a, ha, b, rfl⟩ := h X R hR g
  exact (Sieve.generate R).downward_closed (Sieve.le_generate R _ _ ha) b

theorem restricted_le {D : Type*} [Category D] (F : C ⥤ D) [F.Full] [F.Faithful]
    (J : GrothendieckTopology D) (hJ : J ≤ topology (F.obj P)) :
    F.restrictedTopology J ≤ topology P := by
  apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
  intro X R hR
  change Sieve.generate (R.map F) ∈ J (F.obj X) at hR
  change ∀ g : P ⟶ X, Sieve.generate R g
  intro g
  have hg := hJ _ hR (F.map g)
  rw [Sieve.generate_map_eq_functorPushforward] at hg
  change ((Sieve.generate R).functorPushforward F).functorPullback F g at hg
  rwa [Sieve.functorPullback_functorPushforward_eq] at hg

end OAI.NumberTheory.PadicHodge.IntegralComparison.RepresentablePointTopology
