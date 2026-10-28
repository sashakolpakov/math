import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-! # Difference Constraints -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.DifferenceConstraints.Construction

noncomputable section

/-! A finite system of bounded directed differences is uniformly
close to the corresponding system of exact order inequalities. -/

open scoped Classical

theorem difference_bound_along_path {ι : Type*} (r : ι → ι → Prop) (t : ℝ) (ht : 0 ≤ t)
    {i j : ι} (hij : Relation.ReflTransGen r i j) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ι → ℝ, (∀ a b, r a b → x a - x b ≤ t) → x i - x j ≤ c := by
  induction hij with
  | refl => exact ⟨0, le_rfl, fun _ _ => by simp⟩
  | @tail j k _ hjk ih =>
    obtain ⟨c, hc, hbound⟩ := ih
    refine ⟨c + t, add_nonneg hc ht, fun x hx => ?_⟩
    have h₁ := hbound x hx
    have h₂ := hx j k hjk
    linarith

theorem finite_reachable_difference_bound {ι : Type*} [Finite ι]
    (r : ι → ι → Prop) (t : ℝ) (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ι → ℝ, (∀ a b, r a b → x a - x b ≤ t) →
      ∀ i j, Relation.ReflTransGen r i j → x i - x j ≤ c := by
  let : Fintype ι := Fintype.ofFinite ι
  have hp : ∀ i j : ι, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ι → ℝ,
      (∀ a b, r a b → x a - x b ≤ t) → Relation.ReflTransGen r i j → x i - x j ≤ c := by
    intro i j
    by_cases hij : Relation.ReflTransGen r i j
    · obtain ⟨c, hc, hb⟩ := difference_bound_along_path r t ht hij
      exact ⟨c, hc, fun x hx _ => hb x hx⟩
    · exact ⟨0, le_rfl, fun _ _ h => (hij h).elim⟩
  choose c hc hb using hp
  obtain ⟨C, hC⟩ := (Set.finite_range (fun p : ι × ι => c p.1 p.2)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun x hx i j hij => ?_⟩
  exact (hb i j x hx hij).trans ((hC ⟨(i, j), rfl⟩).trans (le_max_left _ _))

theorem finite_difference_constraints_approximation {ι : Type*} [Fintype ι]
    (r : ι → ι → Prop) (t : ℝ) (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ι → ℝ, (∀ a b, r a b → x a - x b ≤ t) →
      ∃ y : ι → ℝ, (∀ i j, r i j → y i ≤ y j) ∧
        ∀ i, 0 ≤ x i - y i ∧ x i - y i ≤ c := by
  obtain ⟨c, hc, hb⟩ := finite_reachable_difference_bound r t ht
  refine ⟨c, hc, fun x hx => ?_⟩
  let R := Relation.ReflTransGen r
  let S : ι → Finset ℝ := fun i => (Finset.univ.filter (R i)).image x
  have hS : ∀ i, (S i).Nonempty := by
    intro i
    exact ⟨x i, Finset.mem_image.mpr ⟨i,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩, rfl⟩⟩
  let y := fun i => (S i).min' (hS i)
  have hy : ∀ i, ∃ j, R i j ∧ y i = x j := by
    intro i
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp ((S i).min'_mem (hS i))
    exact ⟨j, (Finset.mem_filter.mp hj).2, he.symm⟩
  refine ⟨y, ?_, ?_⟩
  · intro i j hij
    obtain ⟨k, hjk, he⟩ := hy j
    rw [he]
    apply (S i).min'_le
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Relation.ReflTransGen.single hij).trans hjk⟩, rfl⟩
  · intro i
    constructor
    · have hle : y i ≤ x i := (S i).min'_le _ (Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩, rfl⟩)
      linarith
    · obtain ⟨j, hij, he⟩ := hy i
      rw [he]
      exact hb x hx i j hij

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.DifferenceConstraints.Construction
