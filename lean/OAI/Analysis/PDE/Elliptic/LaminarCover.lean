import OAI.Analysis.PDE.Elliptic.GrowthBalls

open Set _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {X I : Type*}

def maximalMembers (Q : I → Set X) (S : Set I) : Set I :=
  {i | i ∈ S ∧ ∀ j ∈ S, Q i ⊆ Q j → j = i}

/-- A rank which strictly decreases under proper enlargement makes
every eligible member lie in an eligible maximal member. -/
theorem exists_maximal_member (Q : I → Set X) (rank : I → ℕ) (S : Set I)
    (hrank : ∀ i j, Q i ⊆ Q j → j ≠ i → rank j < rank i)
    {i : I} (hi : i ∈ S) :
    ∃ j ∈ maximalMembers Q S, Q i ⊆ Q j := by
  suffices h : ∀ n i, rank i = n → i ∈ S → ∃ j ∈ maximalMembers Q S, Q i ⊆ Q j by
    exact h (rank i) i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i hir hi
    by_cases hm : ∀ j ∈ S, Q i ⊆ Q j → j = i
    · exact ⟨i, ⟨hi, hm⟩, Subset.rfl⟩
    · push Not at hm
      obtain ⟨j, hj, hij, hji⟩ := hm
      have hlt : rank j < n := hir ▸ hrank i j hij hji
      obtain ⟨k, hk, hjk⟩ := ih (rank j) hlt j rfl hj
      exact ⟨k, hk, hij.trans hjk⟩

theorem maximalMembers_pairwiseDisjoint (Q : I → Set X) (S : Set I)
    (hlaminar : ∀ i j, Disjoint (Q i) (Q j) ∨ Q i ⊆ Q j ∨ Q j ⊆ Q i) :
    (maximalMembers Q S).PairwiseDisjoint Q := by
  intro i hi j hj hne
  rcases hlaminar i j with hdisj | hij | hji
  · exact hdisj
  · exact (hne (hi.2 j hj.1 hij).symm).elim
  · exact (hne (hj.2 i hi.1 hji)).elim

theorem maximalMembers_cover (Q : I → Set X) (rank : I → ℕ) (S : Set I)
    (hrank : ∀ i j, Q i ⊆ Q j → j ≠ i → rank j < rank i)
    {A : Set X} (hcover : A ⊆ ⋃ i ∈ S, Q i) :
    A ⊆ ⋃ i : maximalMembers Q S, Q i := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
  obtain ⟨j, hj, hij⟩ := exists_maximal_member Q rank S hrank hi
  exact mem_iUnion.mpr ⟨⟨j, hj⟩, hij hxi⟩

/-- Countable ranked laminar covering estimate. The maximal-member
selection, disjointness, and summation are conclusions, not inputs. -/
theorem measure_le_mul_of_ranked_laminar_cover [MeasurableSpace X] [Countable I]
    (μ : Measure X) (Q : I → Set X) (rank : I → ℕ) (S : Set I)
    (hrank : ∀ i j, Q i ⊆ Q j → j ≠ i → rank j < rank i)
    (hlaminar : ∀ i j, Disjoint (Q i) (Q j) ∨ Q i ⊆ Q j ∨ Q j ⊆ Q i)
    (hmeas : ∀ i, MeasurableSet (Q i)) {A B : Set X} {theta : ℝ≥0∞}
    (hcover : A ⊆ ⋃ i ∈ S, Q i)
    (hsub : ∀ i ∈ S, Q i ⊆ B)
    (hdensity : ∀ i ∈ S, μ (A ∩ Q i) ≤ theta * μ (Q i)) :
    μ A ≤ theta * μ B := by
  let M := maximalMembers Q S
  have hc : A ⊆ ⋃ i : M, A ∩ Q i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (maximalMembers_cover Q rank S hrank hcover hx)
    exact mem_iUnion.mpr ⟨i, hx, hi⟩
  have hp : Pairwise (fun i j : M ↦ Disjoint (Q i) (Q j)) := by
    intro i j hij
    exact maximalMembers_pairwiseDisjoint Q S hlaminar i.property j.property
      (fun h ↦ hij (Subtype.ext h))
  have hU : (⋃ i : M, Q i) ⊆ B := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hsub i i.property.1 hi
  calc
    μ A ≤ μ (⋃ i : M, A ∩ Q i) := measure_mono hc
    _ ≤ ∑' i : M, μ (A ∩ Q i) := measure_iUnion_le _
    _ ≤ ∑' i : M, theta * μ (Q i) := ENNReal.tsum_le_tsum fun i ↦ hdensity i i.property.1
    _ = theta * (∑' i : M, μ (Q i)) := ENNReal.tsum_mul_left
    _ = theta * μ (⋃ i : M, Q i) := by rw [measure_iUnion hp (fun i ↦ hmeas i)]
    _ ≤ theta * μ B := mul_le_mul_of_nonneg_left (measure_mono hU) zero_le

end OAI.Analysis.PDE.Elliptic
