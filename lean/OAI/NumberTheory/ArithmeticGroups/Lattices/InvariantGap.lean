import Mathlib

/-! # Invariant Gap -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap.Construction

noncomputable section

/-! Discrete nonzero invariant values keep vectors uniformly away from zero. -/

open scoped Classical
open Set _root_.Metric

theorem uniform_gap_of_discrete_values
    {E F : Type*} [NormedAddCommGroup E] [TopologicalSpace F] [Zero F]
    (P : E → F) (hP : Continuous P) (hP0 : P 0 = 0)
    (D : Set F) (hD : IsDiscrete D) (hD0 : (0 : F) ∈ D)
    (S : Set E) (hvalues : ∀ x ∈ S, P x ∈ D ∧ P x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε ≤ ‖x‖ := by
  obtain ⟨U, hU, hUD⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hD 0 hD0
  have hU0 : (0 : F) ∈ U := by
    have h : (0 : F) ∈ U ∩ D := hUD.symm ▸ mem_singleton 0
    exact h.1
  have hpre : IsOpen (P ⁻¹' U) := hU.preimage hP
  have hpre0 : (0 : E) ∈ P ⁻¹' U := by simpa only [mem_preimage, hP0] using hU0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hpre 0 hpre0
  refine ⟨ε, hε, fun x hx => ?_⟩
  by_contra hle
  have hxball : x ∈ Metric.ball 0 ε := by simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hle
  have hPxU : P x ∈ U := hball hxball
  have hPx0 : P x = 0 := mem_singleton_iff.mp (hUD ▸ ⟨hPxU, (hvalues x hx).1⟩)
  exact (hvalues x hx).2 hPx0

theorem uniform_gap_of_discrete_invariant
    {E F A : Type*} [NormedAddCommGroup E] [TopologicalSpace F] [Zero F]
    (ρ : A → E → E) (P : E → F) (hP : Continuous P) (hP0 : P 0 = 0)
    (D : Set F) (hD : IsDiscrete D) (hD0 : (0 : F) ∈ D)
    (L : Set E) (hvalues : ∀ x ∈ L, x ≠ 0 → P x ∈ D ∧ P x ≠ 0)
    (hinvariant : ∀ a x, x ∈ L → P (ρ a x) = P x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a x, x ∈ L → x ≠ 0 → ε ≤ ‖ρ a x‖ := by
  let S := {y : E | ∃ a x, x ∈ L ∧ x ≠ 0 ∧ y = ρ a x}
  have hv : ∀ y ∈ S, P y ∈ D ∧ P y ≠ 0 := by
    rintro _ ⟨a, x, hx, hx0, rfl⟩
    rw [hinvariant a x hx]
    exact hvalues x hx hx0
  obtain ⟨ε, hε, hgap⟩ := uniform_gap_of_discrete_values P hP hP0 D hD hD0 S hv
  exact ⟨ε, hε, fun a x hx hx0 => hgap (ρ a x) ⟨a, x, hx, hx0, rfl⟩⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap.Construction
