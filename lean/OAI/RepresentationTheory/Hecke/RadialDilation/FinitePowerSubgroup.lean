import Mathlib

/-! # Finite Power Subgroup -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePowerSubgroup.Realization

noncomputable section

/-! Finite families of eventual subgroup members have a common positive power. -/

open scoped Classical

theorem common_positive_power_mem_subgroup {I G : Type*} [Fintype I] [Group G]
    (H : Subgroup G) (g : I → G) (hg : ∀ i, ∃ m : ℕ, 0 < m ∧ g i ^ m ∈ H) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, g i ^ N ∈ H := by
  choose m hm hmem using hg
  let N := ∏ i, m i
  refine ⟨N, Finset.prod_pos (fun i _ => hm i), ?_⟩
  intro i
  have hdiv : m i ∣ N := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hpow : g i ^ N = (g i ^ m i) ^ (N / m i) := by
    rw [← pow_mul, Nat.mul_div_cancel' hdiv]
  rw [hpow]
  exact H.pow_mem (hmem i) _

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePowerSubgroup.Realization
