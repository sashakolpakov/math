import Mathlib

/-! The disjoint stopping-cube argument for finite dyadic families.
The combinatorial results are stated for measurable laminar set families, so
they apply to dyadic cubes without depending on a coordinate convention. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

/-- Dyadic cubes are either nested or disjoint. -/
def IsLaminar {X : Type*} (s : Finset (Set X)) : Prop :=
  ∀ A ∈ s, ∀ B ∈ s, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

noncomputable def maximalSets {X : Type*} (s : Finset (Set X)) : Finset (Set X) := by
  classical
  exact s.filter (fun A => Maximal (· ∈ s) A)

theorem mem_maximalSets {X : Type*} {s : Finset (Set X)} {A : Set X} :
    A ∈ maximalSets s ↔ Maximal (· ∈ s) A := by
  classical
  simp only [maximalSets, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨h.1, h⟩⟩

theorem maximalSets_subset {X : Type*} (s : Finset (Set X)) : maximalSets s ⊆ s := by
  intro A hA
  exact (mem_maximalSets.mp hA).1

/-- Stopping at maximal members does not change the union. -/
theorem iUnion_maximalSets {X : Type*} (s : Finset (Set X)) :
    (⋃ A ∈ maximalSets s, A) = ⋃ A ∈ s, A := by
  apply Subset.antisymm
  · exact iUnion₂_mono' (fun A hA => ⟨A, maximalSets_subset s hA, Subset.rfl⟩)
  · intro x hx
    rcases mem_iUnion₂.mp hx with ⟨A, hA, hxA⟩
    obtain ⟨B, hAB, hB⟩ := s.exists_le_maximal hA
    exact mem_iUnion₂.mpr ⟨B, mem_maximalSets.mpr hB, hAB hxA⟩

/-- The stopping members of a dyadic family are pairwise disjoint. -/
theorem maximalSets_pairwiseDisjoint {X : Type*} {s : Finset (Set X)}
    (hs : IsLaminar s) : (maximalSets s : Set (Set X)).PairwiseDisjoint id := by
  intro A hA B hB hne
  have hA' := mem_maximalSets.mp hA
  have hB' := mem_maximalSets.mp hB
  rcases hs A hA'.1 B hB'.1 with hAB | hBA | hd
  · exact (hne (Subset.antisymm hAB (hA'.2 hB'.1 hAB))).elim
  · exact (hne (Subset.antisymm (hB'.2 hA'.1 hBA) hBA)).elim
  · exact hd

theorem IsLaminar.mono {X : Type*} {s t : Finset (Set X)}
    (hs : IsLaminar s) (ht : t ⊆ s) : IsLaminar t :=
  fun A hA B hB => hs A (ht hA) B (ht hB)

/-- The exact weak `(1,1)` stopping-cube inequality, including the localization
of its right-hand side to the selected union. -/
theorem laminar_weak_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s : Finset (Set X)} (hs : IsLaminar s)
    (hm : ∀ A ∈ s, MeasurableSet A) (f : X → ℝ≥0∞) (t : ℝ≥0∞)
    (hhigh : ∀ A ∈ s, t * μ A ≤ ∫⁻ x in A, f x ∂μ) :
    t * μ (⋃ A ∈ s, A) ≤ ∫⁻ x in ⋃ A ∈ s, A, f x ∂μ := by
  let u := maximalSets s
  have hu : (u : Set (Set X)).PairwiseDisjoint id := maximalSets_pairwiseDisjoint hs
  have hum : ∀ A ∈ u, MeasurableSet A := fun A hA => hm A (maximalSets_subset s hA)
  rw [← iUnion_maximalSets s]
  change t * μ (⋃ A ∈ u, A) ≤ ∫⁻ x in ⋃ A ∈ u, A, f x ∂μ
  have hmeasure : μ (⋃ A ∈ u, A) = ∑ A ∈ u, μ A := by
    simpa only [id_eq] using measure_biUnion_finset (μ := μ) hu hum
  have hintegral : (∫⁻ x in ⋃ A ∈ u, A, f x ∂μ) = ∑ A ∈ u, ∫⁻ x in A, f x ∂μ := by
    simpa only [id_eq] using lintegral_biUnion_finset (μ := μ) hu hum f
  rw [hmeasure, hintegral, Finset.mul_sum]
  exact Finset.sum_le_sum (fun A hA => hhigh A (maximalSets_subset s hA))

end OAI.Analysis.Fourier.SquareFunction
