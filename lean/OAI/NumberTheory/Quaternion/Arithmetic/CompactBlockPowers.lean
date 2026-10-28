import OAI.NumberTheory.Quaternion.Arithmetic.IntegralCompact
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Separation.Profinite

/-! # Compact Block Powers -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CompactBlockPowers

noncomputable section

section

/-! A compact totally disconnected group admits one positive exponent
that sends every element into any prescribed identity neighborhood. -/

open scoped Classical
open Set _root_.Topology

theorem compact_group_exists_uniform_power
    {C : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
    [CompactSpace C] [T2Space C] [TotallyDisconnectedSpace C]
    (U : Set C) (hU : U ∈ 𝓝 (1 : C)) :
    ∃ N : ℕ, 0 < N ∧ ∀ c : C, c ^ N ∈ U := by
  obtain ⟨V, ⟨h1V, hV⟩, hVU⟩ := (nhds_basis_clopen (1 : C)).mem_iff.mp hU
  obtain ⟨K, hKV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hV h1V
  have hi := IntegralCompact.finiteIndex_of_open_in_compact_group K.toSubgroup K.isOpen
  refine ⟨K.toSubgroup.index.factorial, Nat.factorial_pos _, fun c => hVU (hKV ?_)⟩
  exact K.toSubgroup.pow_mem_of_index_ne_zero_of_dvd hi.index_ne_zero c
    (fun m hm hle => Nat.dvd_factorial hm hle)

end

/-! A local block projection preserving a closed subgroup near the
identity also preserves fixed positive powers from the closure of an
arithmetic projection, when the other factors are compact. -/

open scoped Classical
open Set Filter _root_.Topology

section

theorem compact_factor_eventually_power_mem
    {C B L : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
    [CompactSpace C] [T2Space C] [TotallyDisconnectedSpace C]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (e : C × B →* L) (he : Continuous e) (j : B →* L) (hj : Continuous j)
    (m : L →* L) (hm : ∀ c b, m (e (c, b)) = j b)
    (H : Subgroup L) (hH : IsClosed (H : Set L))
    (hnear : ∀ᶠ g in 𝓝 (1 : L), g ∈ H → m g ∈ H)
    (Γ : Subgroup (C × B)) (hΓ : ∀ g ∈ Γ, e g ∈ H) :
    ∃ N : ℕ, 0 < N ∧ ∀ᶠ b in 𝓝 (1 : B),
      b ∈ (Γ.map (MonoidHom.snd C B)).topologicalClosure → j (b ^ N) ∈ H := by
  have ht := he.tendsto (1 : C × B)
  rw [map_one] at ht
  obtain ⟨UC, hUC, VB, hVB, hrect⟩ := mem_nhds_prod_iff.mp (ht hnear)
  obtain ⟨N, hN, hNC⟩ := compact_group_exists_uniform_power UC hUC
  have hp : Tendsto (fun b : B => b ^ N) (𝓝 1) (𝓝 1) := by
    change Tendsto (id ^ N : B → B) (𝓝 1) (𝓝 1)
    simpa only [Pi.pow_apply, id_eq, one_pow] using (continuous_id.pow N).tendsto (1 : B)
  obtain ⟨V, hVsub, hVo, h1V⟩ := mem_nhds_iff.mp (hp hVB)
  let Z : Set B := {b | j (b ^ N) ∈ H}
  have hZ : IsClosed Z := hH.preimage (hj.comp (continuous_id.pow N))
  have hsub : V ∩ (Γ.map (MonoidHom.snd C B) : Set B) ⊆ Z := by
    rintro b ⟨hbV, g, hg, rfl⟩
    have hpΓ : e (g.1 ^ N, g.2 ^ N) ∈ H := hΓ (g ^ N) (Γ.pow_mem hg N)
    have hVpow : g.2 ^ N ∈ VB := hVsub hbV
    have hpH := hrect (show (g.1 ^ N, g.2 ^ N) ∈ UC ×ˢ VB from ⟨hNC g.1, hVpow⟩) hpΓ
    change j (g.2 ^ N) ∈ H
    rw [hm] at hpH
    exact hpH
  have hcl := closure_minimal hsub hZ
  refine ⟨N, hN, ?_⟩
  filter_upwards [hVo.mem_nhds h1V] with b hb hP
  exact hcl (hVo.inter_closure ⟨hb, hP⟩)

end

theorem compact_factor_eventually_power_mem_of_open_projection
    {C B L : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C]
    [CompactSpace C] [T2Space C] [TotallyDisconnectedSpace C]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    (e : C × B →* L) (he : Continuous e) (j : B →* L) (hj : Continuous j)
    (m : L →* L) (hm : ∀ c b, m (e (c, b)) = j b)
    (H : Subgroup L) (hH : IsClosed (H : Set L))
    (hnear : ∀ᶠ g in 𝓝 (1 : L), g ∈ H → m g ∈ H)
    (Γ : Subgroup (C × B)) (hΓ : ∀ g ∈ Γ, e g ∈ H)
    (hP : IsOpen ((Γ.map (MonoidHom.snd C B)).topologicalClosure : Set B)) :
    ∃ N : ℕ, 0 < N ∧ ∀ᶠ b in 𝓝 (1 : B), j (b ^ N) ∈ H := by
  obtain ⟨N, hN, hpow⟩ := compact_factor_eventually_power_mem e he j hj m hm H hH hnear Γ hΓ
  let P := (Γ.map (MonoidHom.snd C B)).topologicalClosure
  have hPnear : (P : Set B) ∈ 𝓝 1 := hP.mem_nhds P.one_mem
  refine ⟨N, hN, ?_⟩
  filter_upwards [hpow, hPnear] with b hb hPmem
  exact hb hPmem

end

end OAI.NumberTheory.Quaternion.Arithmetic.CompactBlockPowers
