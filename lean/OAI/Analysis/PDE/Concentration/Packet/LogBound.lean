import OAI.Analysis.PDE.Concentration.LogarithmicScale

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

/-- The normalized restricted-type packet estimate with the manuscript's
exact logarithmic exponent. The physical dimension is `n+2`; after taking
the critical root, the logarithmic loss is `3*(n+5)/2`. -/
theorem normalized_packet_logarithmic_bound {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
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
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      (∀ b < (1 : ℝ), ∃ y, b < ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) →
      ∀ _ : PhysicalPacketSolution R h (h * packetLogScale D h)
        κ cR cI v (largeBackground (n + 1) h),
      (∫ t in (1 : ℝ)..2, ∫ y in physicalSpatialCell R,
        ‖packetBaseWave κ cR cI v (physicalNullTime (n + 1) t) y‖ ^
          (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1)))) ≤
      C * (1 + Real.log h⁻¹) ^
        ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) * (3 * ((n : ℝ) + 5) / 2)) *
        (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) := by
  obtain ⟨c, C, h₀, L₀, B, hc, hC, hh₀, hh₀1, hL₀, hB, hmain⟩ :=
    normalized_packet_concentration hK hpos hcap A hA
  obtain ⟨D, h₁, hD, hh₁, hh₁1, hscale⟩ := exists_packet_log_scale L₀ B
  refine ⟨(C / c) * D ^ (3 * ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 1)), D,
    min h₀ h₁, by positivity, hD, lt_min hh₀ hh₁, (min_le_left _ _).trans hh₀1, ?_⟩
  intro R hR h hh hsmall ι inst κ cR cI v m hinj hκ hm hf hs hnorm hnorm' S
  have hh₀' := hsmall.trans (min_le_left h₀ h₁)
  obtain ⟨hL, hlog, ha⟩ := hscale h hh (hsmall.trans (min_le_right h₀ h₁))
  have hestimate := hmain R hR h (packetLogScale D h) hh hh₀' hL hlog ha κ cR cI v m
    hinj hκ hm hf hs hnorm hnorm' S
  exact packet_log_scale_bound n hc hC.le hD hh (hh₀'.trans hh₀1)
    (integral_nonneg fun _ => sq_nonneg _) ha hestimate

end OAI.Analysis.PDE.Concentration
