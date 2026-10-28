import OAI.NumberTheory.Quaternion.Arithmetic.TangentCone
import Mathlib.Algebra.Ring.GeomSum

/-! # Tangent Powers -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.TangentPowers

noncomputable section

/-! Positive powers preserve tangent spans in characteristic zero.
The argument uses a finite geometric sum and continuity of multiplication,
so it also applies to products with differently normalized local norms. -/

open scoped Classical
open Set Filter _root_.Topology

variable {κ A : Type*} [Field κ] [Ring A] [Algebra κ A]

theorem scaled_power_displacement (N : ℕ) (c : κ) (d : A) :
    c • ((1 + d) ^ N - 1) =
      (∑ j ∈ Finset.range N, (1 + d) ^ j) * (c • d) := by
  rw [← geom_sum_mul, mul_smul_comm]
  congr 2
  abel

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem power_mapsTo_tangentCone_of_eventually
    (s t : Set A) (N : ℕ) (hpow : ∀ᶠ x in 𝓝 (1 : A), x ∈ s → x ^ N ∈ t) :
    MapsTo (fun a : A => (N : κ) • a) (tangentConeAt κ s 1) (tangentConeAt κ t 1) := by
  intro a ha
  obtain ⟨α, l, hl, c, d, hd, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt ha
  have ht : Tendsto (fun x => (1 : A) + d x) l (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hd
  have hp : Tendsto (fun x => ((1 : A) + d x) ^ N - 1) l (𝓝 0) := by
    simpa only [one_pow, sub_self] using (ht.pow N).sub (tendsto_const_nhds (x := (1 : A)))
  apply mem_tangentConeAt_of_seq l c (fun x => (1 + d x) ^ N - 1) hp
  · filter_upwards [hds, ht hpow] with x hx hpx
    have he : 1 + ((1 + d x) ^ N - 1) = (1 + d x) ^ N := by abel
    exact he.symm ▸ hpx hx
  · have hs : Continuous (fun z : A => ∑ j ∈ Finset.range N, z ^ j) := by fun_prop
    have hlim := (hs.tendsto 1 |>.comp ht).mul hcd
    simpa only [Function.comp_def, scaled_power_displacement, one_pow, Finset.sum_const,
      Finset.card_range, smul_mul_assoc, one_mul, Nat.cast_smul_eq_nsmul] using hlim

theorem tangentSpan_le_of_eventually_pow_mem [CharZero κ]
    (s t : Set A) (N : ℕ) (hN : 0 < N)
    (hpow : ∀ᶠ x in 𝓝 (1 : A), x ∈ s → x ^ N ∈ t) :
    Submodule.span κ (tangentConeAt κ s 1) ≤ Submodule.span κ (tangentConeAt κ t 1) := by
  apply Submodule.span_le.mpr
  intro a ha
  change a ∈ Submodule.span κ (tangentConeAt κ t 1)
  have hna : (N : κ) • a ∈ Submodule.span κ (tangentConeAt κ t 1) :=
    Submodule.subset_span (power_mapsTo_tangentCone_of_eventually (κ := κ) s t N hpow ha)
  have hc : (N : κ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hm := (Submodule.span κ (tangentConeAt κ t 1)).smul_mem (N : κ)⁻¹ hna
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hm

omit [IsTopologicalRing A] in
theorem eventually_group_pow_image_mem
    {L : Type*} [Group L] [TopologicalSpace L]
    (e : L →* A) (he : Topology.IsEmbedding e) (H : Subgroup L) (N : ℕ)
    (hpow : ∀ᶠ g in 𝓝 (1 : L), g ^ N ∈ H) :
    ∀ᶠ x in 𝓝 (1 : A), x ∈ range e → x ^ N ∈ e '' (H : Set L) := by
  rw [he.isInducing.nhds_eq_comap (1 : L), map_one] at hpow
  obtain ⟨V, hV, hVH⟩ := Filter.mem_comap.mp hpow
  filter_upwards [hV] with x hx hrange
  obtain ⟨g, rfl⟩ := hrange
  exact ⟨g ^ N, hVH hx, map_pow e g N⟩

theorem tangentSpan_le_of_eventually_group_pow_mem [CharZero κ]
    {L : Type*} [Group L] [TopologicalSpace L]
    (e : L →* A) (he : Topology.IsEmbedding e) (H : Subgroup L) (N : ℕ) (hN : 0 < N)
    (hpow : ∀ᶠ g in 𝓝 (1 : L), g ^ N ∈ H) :
    Submodule.span κ (tangentConeAt κ (range e) 1) ≤
      Submodule.span κ (tangentConeAt κ (e '' (H : Set L)) 1) :=
  tangentSpan_le_of_eventually_pow_mem _ _ N hN
    (eventually_group_pow_image_mem e he H N hpow)

end

end OAI.NumberTheory.Quaternion.Arithmetic.TangentPowers
