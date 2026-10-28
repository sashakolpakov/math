import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Order.Minimal

/-! # Monomial Termination -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTermination.Construction

/-! Minimal coordinate centers and a decreasing exponent measure for monomial controlled transforms. -/

open Finset

variable {σ : Type*} [DecidableEq σ]

/-- A permissible coordinate center minimal under removal of a coordinate. -/
def MinimalMonomialCenter (a : σ → ℕ) (b : ℕ) (C : Finset σ) : Prop :=
  C.Nonempty ∧ b ≤ ∑ i ∈ C, a i ∧ ∀ i ∈ C, ∑ j ∈ C.erase i, a j < b

/-- Every permissible finite coordinate set contains a minimal permissible center. -/
theorem exists_minimal_monomial_center (a : σ → ℕ) (b : ℕ) (hb : 0 < b)
    (s : Finset σ) (hs : b ≤ ∑ i ∈ s, a i) :
    ∃ C ⊆ s, MinimalMonomialCenter a b C := by
  obtain ⟨C, hCs, hC⟩ := exists_minimal_le_of_wellFoundedLT
    (fun C : Finset σ => b ≤ ∑ i ∈ C, a i) s hs
  refine ⟨C, hCs, ?_, hC.1, ?_⟩
  · by_contra h
    have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hz := hC.1
    simp only [he, sum_empty] at hz
    omega
  · intro i hi
    by_contra h
    have hle : C ⊆ C.erase i := hC.2 (Nat.le_of_not_gt h) (erase_subset i C)
    exact (notMem_erase i C) (hle hi)

/-- The new exceptional exponent in the `i`th controlled-transform chart. -/
def monomialChartExponents (a : σ → ℕ) (b : ℕ) (C : Finset σ) (i : σ) : σ → ℕ :=
  Function.update a i ((∑ j ∈ C, a j) - b)

/-- Minimality makes every new exceptional exponent strictly smaller
than the exponent of the coordinate used as denominator. -/
theorem monomial_exceptional_exponent_lt (a : σ → ℕ) (b : ℕ) (C : Finset σ)
    (hC : MinimalMonomialCenter a b C) (i : σ) (hi : i ∈ C) :
    (∑ j ∈ C, a j) - b < a i := by
  have he := sum_erase_add C a hi
  have hlt := hC.2.2 i hi
  have hle := hC.2.1
  omega

variable [Fintype σ]

/-- The sum of all exponents strictly decreases in every chart of a
minimal permissible coordinate blowup. -/
theorem monomialChartExponents_sum_lt (a : σ → ℕ) (b : ℕ) (C : Finset σ)
    (hC : MinimalMonomialCenter a b C) (i : σ) (hi : i ∈ C) :
    (∑ j, monomialChartExponents a b C i j) < ∑ j, a j := by
  have hlt := monomial_exceptional_exponent_lt a b C hC i hi
  have he := sum_erase_add univ a (mem_univ i)
  rw [monomialChartExponents, sum_update_of_mem (mem_univ i), sdiff_singleton_eq_erase]
  omega

/-- One local monomial step, including the choice of an actual denominator chart. -/
def MonomialControlledStep (b : ℕ) (a' a : σ → ℕ) : Prop :=
  ∃ (C : Finset σ) (i : σ), MinimalMonomialCenter a b C ∧ i ∈ C ∧
    a' = monomialChartExponents a b C i

/-- Local monomial controlled transformation cannot continue indefinitely:
every branch decreases the natural-number sum of exponents. -/
theorem monomialControlledStep_wellFounded (b : ℕ) :
    WellFounded (MonomialControlledStep (σ := σ) b) := by
  refine Subrelation.wf ?_ (measure (fun a : σ → ℕ => ∑ i, a i)).wf
  rintro a' a ⟨C, i, hC, hi, rfl⟩
  exact monomialChartExponents_sum_lt a b C hC i hi

end OAI.AlgebraicGeometry.Resolution.Blowups.MonomialTermination.Construction
