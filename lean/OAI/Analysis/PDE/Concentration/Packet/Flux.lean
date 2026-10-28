import OAI.Analysis.PDE.Concentration.Packet.Normalization
import OAI.Analysis.PDE.Concentration.CrudeDensity
import OAI.Analysis.PDE.Concentration.Physical.Extension

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Matrix OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology Matrix.Norms.Elementwise

theorem compact_packet_frequency_lower {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η) :
    ∃ k : ℝ, 0 < k ∧ ∀ {h κ : ℝ} (v : Fin d → ℝ), 0 < h → 0 < κ →
      h • packetSpatialFrequency κ v ∈ K → k / h ≤ κ := by
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, zero_lt_one, ?_⟩
    intro h κ v hh hκ hmem
    simp only [hK0, mem_empty_iff_false] at hmem
  obtain ⟨η, hη, hmin⟩ := hK.exists_isMinOn hKne continuous_gaussianFrequencyK.continuousOn
  refine ⟨gaussianFrequencyK η, hpos η hη, ?_⟩
  intro h κ v hh hκ hmem
  have hb := hmin hmem
  change gaussianFrequencyK η ≤ gaussianFrequencyK (h • packetSpatialFrequency κ v) at hb
  rw [gaussianFrequencyK_smul hh.le, gaussianFrequencyK_packet hκ.le] at hb
  exact (div_le_iff₀ hh).mpr (by simpa only [mul_comm] using hb)

theorem packet_flux_prefactor_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (h N F : ℝ) (hh : 0 < h) (_ : 0 ≤ N) (hF : 0 ≤ F)
    (hcount : (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1)) :
    (Fintype.card ι : ℝ) * ((d : ℝ) + 1) * (F / h ^ 2) ^ ((d : ℝ) / 2) ≤
      (N * ((d : ℝ) + 1) * F ^ ((d : ℝ) / 2)) / h ^ (2 * d + 1) := by
  rw [OAI.Analysis.Calculus.Current.scale_rpow_half h F d hh hF]
  have hb := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ ((d : ℝ) + 1) * (F ^ ((d : ℝ) / 2) / h ^ d) by positivity)
  convert hb using 1
  · ring
  · rw [show 2 * d + 1 = (d + 1) + d by omega, pow_add]
    ring

/-- The physical normal flux is smaller than any prescribed power of h
once the cylinder scale has the source's logarithmic lower bound. -/
theorem normalized_packet_boundary_flux {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (J : ℕ) :
    ∃ h₀ B : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < B ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ {ι : Type} [Fintype ι] (h L : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
      (m : ι → Option (Fin d) → ℤ),
      0 < h → h ≤ h₀ → 1 ≤ L → B * Real.log h⁻¹ ≤ L →
      Function.Injective m → (∀ j, 0 < κ j) →
      (∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
        (m j i : ℝ) * (2 * Real.pi) / 100) →
      (∀ j, h • packetSpatialFrequency (κ j) (v j) ∈ K) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      ∀ x, h * L ≤ ‖(OAI.Analysis.PDE.Green.fullPhysicalProjection d x).1‖ → OAI.Analysis.PDE.Green.physicalFullDefining d (h * L) x = 0 →
        ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d (h * L)) x) ᵥ*
          physicalLatticeCurrent R h (h * L) κ cR cI v x‖ ≤
            (40 * ((d : ℝ) + 2) * ((d : ℝ) + 1) ^ 2) * h ^ J := by
  obtain ⟨N, hN, hcount⟩ := compact_angular_frequency_count hK
  obtain ⟨F, hF, hfreq⟩ := compact_packet_frequency_bound hK
  obtain ⟨k, hk, hlow⟩ := compact_packet_frequency_lower hK hpos
  let P := N * ((d : ℝ) + 1) * F ^ ((d : ℝ) / 2)
  obtain ⟨h₀, hh₀, hh₀1, habs⟩ := exists_crude_absorption_scale (2 * d + 1) (2 * d + 2)
    (by omega) (show 0 ≤ P by dsimp [P]; positivity)
  let b : ℝ := (2 * d + 2 : ℕ)
  let M : ℝ := (J : ℝ) + 1
  let B := 3200 * (b + M / 2) / k
  have hb : 0 < b := by dsimp [b]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨h₀, B, hh₀, hh₀1, hB, ?_⟩
  intro R hR ι inst h L κ cR cI v m hh hsmall hL hlog hinj hκ hm hf hnorm x ht hr
  have hh1 := hsmall.trans hh₀1
  have hha : h ≤ h * L := by nlinarith
  have ha : 0 < h * L := hh.trans_le hha
  have hy := physicalNullHeight_on_closed_fiber d (h * L) ha x ht hr.le
  have hcard : (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1) := by
    apply (le_div_iff₀ (pow_pos hh _)).mpr
    exact hcount R hR h hh hh1 _ m hinj hf hm
  have hpref : (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      ((F / h ^ 2) ^ ((d : ℝ) / 2) * 1) ≤ h ^ (-b) := by
    rw [mul_one]
    have hp := (packet_flux_prefactor_bound h N F hh hN.le hF.le hcard).trans (habs h hh hsmall)
    simpa only [b, Real.rpow_neg hh.le, Real.rpow_natCast, one_div] using hp
  have hdecay : (b + M / 2) * Real.log h⁻¹ ≤
      (k / h) * ‖(physicalToNullCurrentPoint d x).2 none‖ / 3200 := by
    have hs := mul_le_mul_of_nonneg_left hlog (show 0 ≤ k / 3200 by positivity)
    have he : k / 3200 * (B * Real.log h⁻¹) = (b + M / 2) * Real.log h⁻¹ := by
      dsimp only [B]
      field_simp
    rw [he] at hs
    have ht' := mul_le_mul_of_nonneg_left hy (show 0 ≤ k / h / 3200 by positivity)
    have he' : k / h / 3200 * (h * L) = k / 3200 * L := by field_simp
    rw [he'] at ht'
    exact hs.trans (by convert ht' using 1 ; dsimp only [physicalNullHeight] ; ring)
  have hflux := physicalLatticeCurrent_lateral_power_flux_bound R h (h * L) (F / h ^ 2) 1
    (k / h) b M hh hha (by positivity) (by norm_num) κ cR cI v hκ
    (fun j => hlow (v j) hh (hκ j) (hf j)) x hy
    (fun j => OAI.Analysis.Calculus.Current.frequency_over_height_bound h F (κ j) _ hh (hκ j).le
      (hfreq (v j) hh (hκ j) (hf j)) (hha.trans hy))
    (packet_coefficient_le_one R κ cR cI v m hinj hm hnorm)
    (fun j => packet_velocity_bound (v j) hh (hκ j) (hcap _ (hf j))) hr hpref hdecay
  simpa only [M, add_sub_cancel_right, Real.rpow_natCast] using hflux

end OAI.Analysis.PDE.Concentration
