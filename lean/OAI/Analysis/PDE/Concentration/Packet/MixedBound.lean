import OAI.Analysis.PDE.Concentration.Packet.LogBound
import OAI.Analysis.PDE.Concentration.Packet.Scaling
import OAI.Analysis.PDE.Concentration.Packet.Zero

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

theorem recover_homogeneous_estimate {P p C W E : ℝ} (hP : 0 < P)
    (hb : (P⁻¹) ^ p * W ≤ C * ((P⁻¹) ^ 2 * E)) :
    W ≤ C * P ^ (p - 2) * E := by
  have hp : 0 < (P⁻¹) ^ p := Real.rpow_pos_of_pos (inv_pos.mpr hP) p
  have he : (P⁻¹) ^ p * (C * P ^ (p - 2) * E) = C * ((P⁻¹) ^ 2 * E) := by
    rw [Real.rpow_sub hP, Real.inv_rpow hP.le, Real.rpow_two]
    field_simp
  rw [← he] at hb
  nlinarith

/-- The restricted-type packet estimate for arbitrary coefficients.
The norm is the actual supremum of the initial finite Fourier sum. The only
PDE input is a smooth solution for its normalized packet. -/
theorem packet_mixed_logarithmic_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C D h₀ : ℝ, 0 < C ∧ 1 ≤ D ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ), Function.Injective m →
      (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt (packetLogScale D h) *
        ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      ∀ _ : PhysicalPacketSolution R h (h * packetLogScale D h) κ
        (fun i => (packetSupNorm κ cR cI v)⁻¹ * cR i)
        (fun i => (packetSupNorm κ cR cI v)⁻¹ * cI i) v (largeBackground (n + 1) h),
      (∫ t in (1 : ℝ)..2, ∫ y in physicalSpatialCell R,
        ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) t) y‖ ^
          (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
      C * (1 + Real.log h⁻¹) ^
        ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) * (3 * ((n : ℝ) + 5) / 2)) *
        (packetSupNorm κ cR cI v) ^
          ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) - 2) *
        (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) := by
  obtain ⟨C, D, h₀, hC, hD, hh₀, hh₀1, hmain⟩ :=
    normalized_packet_logarithmic_bound hK hpos hcap A hA
  refine ⟨C, D, h₀, hC, hD, hh₀, hh₀1, ?_⟩
  intro R hR h hh hsmall ι inst κ cR cI v m hinj hκ hm hf hs S
  by_cases hP : 0 < packetSupNorm κ cR cI v
  swap
  · have hP0 : packetSupNorm κ cR cI v = 0 :=
      le_antisymm (le_of_not_gt hP) (packetSupNorm_nonneg κ cR cI v)
    have hw := packet_zero_of_supNorm_zero R κ cR cI v m hinj hm hP0
    have hp : 0 < 2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)) := by positivity
    simp [hw, Real.zero_rpow hp.ne']
  have hb := hmain R hR h hh hsmall κ
    (fun i => (packetSupNorm κ cR cI v)⁻¹ * cR i)
    (fun i => (packetSupNorm κ cR cI v)⁻¹ * cI i) v m hinj hκ hm hf hs
    (normalized_packet_norm_le κ cR cI v hP)
    (fun b hb => normalized_packet_near_sup κ cR cI v hP hb) S
  simp_rw [integral_rpow_packetBaseWave_scale κ cR cI v (inv_nonneg.mpr hP.le)] at hb
  rw [intervalIntegral.integral_const_mul,
    integral_sq_packetBaseWave_scale κ cR cI v (inv_nonneg.mpr hP.le)] at hb
  exact recover_homogeneous_estimate hP hb

end OAI.Analysis.PDE.Concentration
