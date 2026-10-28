import Mathlib.AlgebraicGeometry.Scheme

/-! # Range Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RangeCriterion

/-! A scheme morphism lands in an open subset precisely when its inverse image is the whole source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem range_subset_open_iff_preimage_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Set.range f ⊆ (U : Set Y) ↔ f ⁻¹ᵁ U = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x _
    exact h ⟨x, rfl⟩
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    have hx : x ∈ f ⁻¹ᵁ U := h.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial)
    exact hx

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RangeCriterion
