import Mathlib

/-! # Finite Cover -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FiniteCover.CM

noncomputable section

/-! A compact covering of a connected nonempty base has a constant finite
positive fiber degree. The degree is constructed from the actual fibers. -/

open _root_.TopologicalSpace Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem covering_fiber_card_locally_constant (f : X → Y) (hf : IsCoveringMap f) :
    IsLocallyConstant (fun y => Nat.card (f ⁻¹' {y})) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨hdiscrete, U, hx, hU, hfU, H, hH⟩ := hf x
  refine ⟨U, hU, hx, ?_⟩
  intro y hy
  have he : IsEvenlyCovered f y (f ⁻¹' {x}) :=
    ⟨hdiscrete, U, hy, hU, hfU, H, hH⟩
  exact (Nat.card_congr he.fiberHomeomorph.toEquiv).symm

theorem covering_fiber_finite [T2Space X] [T2Space Y] [CompactSpace X]
    (f : X → Y) (hf : IsCoveringMap f) (y : Y) : Finite (f ⁻¹' {y}) := by
  let : DiscreteTopology (f ⁻¹' {y}) := (hf y).discreteTopology_fiber
  let : CompactSpace (f ⁻¹' {y}) :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage hf.continuous).isCompact
  exact finite_of_compact_of_discrete

theorem covering_positive_degree [T2Space X] [T2Space Y] [CompactSpace X]
    [PreconnectedSpace Y] [Nonempty Y]
    (f : X → Y) (hf : IsCoveringMap f) (hsurj : Function.Surjective f) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Y, Nat.card {x : X // f x = y} = d := by
  classical
  let y₀ : Y := Classical.choice inferInstance
  let : Finite (f ⁻¹' {y₀}) := covering_fiber_finite f hf y₀
  let : Nonempty (f ⁻¹' {y₀}) := by
    obtain ⟨x, hx⟩ := hsurj y₀
    exact ⟨⟨x, hx⟩⟩
  refine ⟨Nat.card (f ⁻¹' {y₀}), Nat.card_pos, ?_⟩
  intro y
  exact (covering_fiber_card_locally_constant f hf).apply_eq_of_isPreconnected
    isPreconnected_univ (Set.mem_univ y) (Set.mem_univ y₀)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FiniteCover.CM
