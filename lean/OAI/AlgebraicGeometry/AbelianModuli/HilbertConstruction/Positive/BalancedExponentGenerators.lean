import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.ExponentFiniteGeneration
import Mathlib.Algebra.Group.Submonoid.Finsupp

/-! # Balanced Exponent Generators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.BalancedExponentGenerators

noncomputable section

/-! Removing the zero exponent from a finite generating set leaves
finite nonzero balanced generators and explicit natural coefficients. -/
open scoped BigOperators Classical
universe u v
variable {κ : Type u} [Fintype κ] {ι : Type v} (w : κ → ι → ℕ)

theorem balancedExponentMonoid_nonzero_generators :
    ∃ (n : ℕ) (B : Fin n → κ → ℕ),
      (∀ j, B j ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w ∧ B j ≠ 0) ∧
      AddSubmonoid.closure (Set.range B) = Balanced.ExponentFiniteGeneration.balancedExponentMonoid w := by
  obtain ⟨s, hs⟩ := Balanced.ExponentFiniteGeneration.balancedExponentMonoid_fg w
  let t := s.erase 0
  have ht : AddSubmonoid.closure (t : Set (κ → ℕ)) = Balanced.ExponentFiniteGeneration.balancedExponentMonoid w := by
    apply le_antisymm
    · apply AddSubmonoid.closure_le.mpr
      intro a ha
      rw [← hs]
      exact AddSubmonoid.subset_closure (Finset.mem_of_mem_erase ha)
    · rw [← hs]
      apply AddSubmonoid.closure_le.mpr
      intro a ha
      by_cases hz : a = 0
      · rw [hz]
        exact AddSubmonoid.zero_mem _
      · exact AddSubmonoid.subset_closure (Finset.mem_erase.mpr ⟨hz, ha⟩)
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let B : Fin (Fintype.card t) → κ → ℕ := fun j => (e j).val
  have hB : Set.range B = (t : Set (κ → ℕ)) := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩
      exact (e j).property
    · intro ha
      exact ⟨e.symm ⟨a, ha⟩, congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)⟩
  refine ⟨Fintype.card t, B, ?_, hB.symm ▸ ht⟩
  intro j
  refine ⟨?_, (Finset.mem_erase.mp (e j).property).1⟩
  rw [← ht]
  exact AddSubmonoid.subset_closure (e j).property

theorem balancedExponentMonoid_positive_generator_representation :
    ∃ (n : ℕ) (B : Fin n → κ → ℕ),
      (∀ j, B j ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w ∧ B j ≠ 0) ∧
      ∀ a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid w, ∃ q : Fin n → ℕ, a = ∑ j, q j • B j := by
  obtain ⟨n, B, hB, hcl⟩ := balancedExponentMonoid_nonzero_generators w
  refine ⟨n, B, hB, ?_⟩
  intro a ha
  exact (AddSubmonoid.mem_closure_range_iff_of_fintype).mp (hcl.symm ▸ ha)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Positive.BalancedExponentGenerators
