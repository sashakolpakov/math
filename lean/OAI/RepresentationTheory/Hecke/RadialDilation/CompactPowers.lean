import Mathlib

/-! # Compact Powers -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.CompactPowers.Realization

noncomputable section

/-! Positive powers of a relatively compact cyclic subgroup return arbitrarily close to identity. -/

open scoped _root_.Topology
open Filter

theorem exists_positive_power_mem_nhds
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [FirstCountableTopology G]
    (g : G) (C : Set G) (hC : IsCompact C) (hg : ∀ n : ℕ, g ^ n ∈ C)
    {U : Set G} (hU : U ∈ 𝓝 (1 : G)) : ∃ N : ℕ, 0 < N ∧ g ^ N ∈ U := by
  obtain ⟨a, _, φ, hφ, hlim⟩ := hC.tendsto_subseq hg
  have hstep : Tendsto (fun n => g ^ φ (n + 1)) atTop (𝓝 a) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n => g ^ φ (n + 1) * (g ^ φ n)⁻¹) atTop (𝓝 (1 : G)) := by
    simpa only [Function.comp_def, mul_inv_cancel] using hstep.mul hlim.inv
  obtain ⟨n, hn⟩ := (hratio.eventually hU).exists
  have hlt : φ n < φ (n + 1) := hφ (Nat.lt_succ_self n)
  refine ⟨φ (n + 1) - φ n, Nat.sub_pos_of_lt hlt, ?_⟩
  rw [pow_sub g hlt.le]
  exact hn

end

end OAI.RepresentationTheory.Hecke.RadialDilation.CompactPowers.Realization
