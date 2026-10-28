import OAI.Analysis.PDE.Concentration.SectorCutoffs
import OAI.Analysis.PDE.Concentration.Input.Geometry
import OAI.Analysis.PDE.Concentration.DensityBounds

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric Filter OAI.Analysis.Calculus.Current
open scoped ContDiff Topology

theorem isOpen_small_velocity (d : ℕ) :
    IsOpen {η : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK η ∧ ‖gaussianVelocity η‖ < 1} := by
  apply isOpen_iff_mem_nhds.mpr
  intro η hη
  have hU : IsOpen {ξ : OAI.Analysis.Calculus.Current.SpatialSpace d | 0 < gaussianFrequencyK ξ} :=
    isOpen_lt continuous_const continuous_gaussianFrequencyK
  have hv := ((contDiffOn_gaussianVelocity η hη.1).contDiffAt (hU.mem_nhds hη.1)).continuousAt
  filter_upwards [hU.mem_nhds hη.1, hv.norm.eventually (Iio_mem_nhds hη.2)] with ξ hξ hvξ
  exact ⟨hξ, hvξ⟩

/-- Recovery cutoffs have genuinely small velocity on their entire support,
not just on the finite set of packet frequencies. -/
theorem exists_recovery_sector_cutoffs {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ K, ‖gaussianVelocity η‖ < 1) (A : ℝ) :
    ∃ (ρ : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ) (χ : TransverseSpace d → ℂ) (Rχ : ℝ),
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ η ∈ tsupport ρ, 0 < gaussianFrequencyK η) ∧
      (∀ η ∈ tsupport ρ, ‖gaussianVelocity η‖ ≤ 1) ∧
      tsupport χ ⊆ closedBall 0 Rχ ∧ (∀ η ∈ K, ρ η = 1) ∧
      (∀ W : TransverseSpace d, ‖W‖ ≤ Real.sqrt 12 * A → χ W = 1) := by
  obtain ⟨ρ, hρ, hcρ, hsρ, heρ⟩ := exists_compact_complex_cutoff hK (isOpen_small_velocity d)
    (fun η hη => ⟨hpos η hη, hv η hη⟩)
  obtain ⟨χ, hχ, hcχ, hsχ, heχ⟩ := exists_compact_complex_cutoff
    (isCompact_closedBall (0 : TransverseSpace d) (Real.sqrt 12 * A))
    (isOpen_ball : IsOpen (ball (0 : TransverseSpace d) (Real.sqrt 12 * A + 1)))
    (closedBall_subset_ball (by linarith))
  refine ⟨ρ, χ, Real.sqrt 12 * A + 1, hρ, hcρ, hχ, hcχ,
    fun η hη => (hsρ hη).1, fun η hη => (hsρ hη).2.le,
    hsχ.trans ball_subset_closedBall, heρ, ?_⟩
  intro W hW
  exact heχ W (by simpa only [mem_closedBall, dist_zero_right] using hW)

theorem output_recovery_power {d : ℕ} {h L : ℝ} (hL : 0 ≤ L) :
    (h ^ d * L ^ ((gaussianDerivativeOrder d : ℝ) / 2 + d / 2)) ^ 2 =
      h ^ (2 * d) * L ^ ((gaussianDerivativeOrder d : ℝ) + d) := by
  rw [mul_pow, ← Real.rpow_mul_natCast hL, ← pow_mul]
  congr 1
  · congr 1 ; omega
  · congr 1
    norm_num
    ring

/-- The true packet recovery estimate, with no auxiliary cutoff hypotheses.
The coefficient is uniform over the scale and the physical fiber. -/
theorem packet_sector_density_recovery {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ K, ‖gaussianVelocity η‖ < 1) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L : ℝ), 0 < h → 10000 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ), (∀ k, 0 < κ k) →
      (∀ k i, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (τ : ℂ), h * L ≤ ‖τ‖ → ‖τ‖ ≤ 4 * (h * L) →
      ∀ q : Option (Fin d) → ℂ, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q ≤ 0 →
      ‖OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) / (h * L : ℝ)‖ ≤ 1 / 100 →
      ‖transverseRatio (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)‖ ≤ 2 * (Real.sqrt L)⁻¹ →
      ∀ y y' : OAI.Analysis.Calculus.Current.SpatialSpace d, ‖y - y'‖ ≤ h →
      ‖packetBaseWave κ cR cI v x y‖ ^ 2 ≤
        C * h ^ (2 * d) * L ^ ((gaussianDerivativeOrder d : ℝ) + d) *
          OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
            (x - nullSpatialShift y') (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)) := by
  obtain ⟨ρ, χ, Rχ, hρ, hcρ, hχ, hcχ, hpρ, hvρ, hsχ, heρ, heχ⟩ :=
    exists_recovery_sector_cutoffs hK hpos hv A
  obtain ⟨C, hC, hb⟩ := packet_density_recovery hρ hcρ hχ hcχ hpρ hvρ Rχ (2 * Real.sqrt 12) hsχ
  let σ : ℝ := (gaussianDerivativeOrder d : ℝ) / 2 + d / 2
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  let P : ℝ := (12 : ℝ) ^ σ
  refine ⟨C ^ 2 * P ^ 2 * 3 ^ (d + 3) + 1, by positivity, ?_⟩
  intro R h L hh hL ι _ κ cR cI v hκ hm hf hs x τ ht ht' q hr hp hW y y' hy
  have hL0 : 0 < L := by linarith
  have ha : 0 < h * L := mul_pos hh hL0
  obtain ⟨hyl, hyu⟩ := physical_input_height (h * L) τ q ha ht ht' hr
  let ℓ := ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ / h
  have hl : L ≤ ℓ := (le_div_iff₀ hh).mpr (by nlinarith)
  have hu : ℓ ≤ 12 * L := (div_le_iff₀ hh).mpr (by nlinarith)
  have he : ‖OAI.Analysis.Calculus.Current.physicalEmbedding τ q none‖ = h * ℓ := by dsimp [ℓ]; field_simp
  have hsqrt : Real.sqrt ℓ ≤ Real.sqrt 12 * Real.sqrt L := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    exact Real.sqrt_le_sqrt hu
  have hRW : Real.sqrt ℓ * ‖transverseRatio (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)‖ ≤ 2 * Real.sqrt 12 := by
    calc
      _ ≤ (Real.sqrt 12 * Real.sqrt L) * (2 * (Real.sqrt L)⁻¹) :=
        mul_le_mul hsqrt hW (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hcut (k : ι) : radialAngularCutoff ρ χ (Real.sqrt ℓ)
      (h • packetSpatialFrequency (κ k) (v k)) = 1 :=
    scaled_sector_cutoff_eq_one hA hL0 (hL0.le.trans hl) hu heχ (heρ _ (hf k)) (hs k)
  have hraw := hb R h ℓ (h * L) hh (by linarith) ha.ne' κ cR cI v hκ x
    (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) he (transverseRatio_norm_le_one (h * L) _ hr) hRW hcut hm hr hp y y' hy
  have hμ : 0 ≤ OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
      (x - nullSpatialShift y') (OAI.Analysis.Calculus.Current.physicalEmbedding τ q)) := by
    have hh' := smoothed_gaussian_zero_le_density R ρ χ hh (by linarith) (h * L) ha.ne'
      κ cR cI v hκ x (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) he hcut hm hr hp y'
    exact (smoothedSquare_nonneg hh _ _).trans hh'
  have hpow : ℓ ^ σ ≤ P * L ^ σ := by
    calc
      _ ≤ (12 * L) ^ σ := Real.rpow_le_rpow (hL0.le.trans hl) hu hσ
      _ = _ := Real.mul_rpow (by norm_num) hL0.le
  have hbpow : (C * h ^ d * ℓ ^ σ) ^ 2 ≤ C ^ 2 * P ^ 2 * (h ^ d * L ^ σ) ^ 2 := by
    have h := pow_le_pow_left₀ (show 0 ≤ C * h ^ d * ℓ ^ σ by positivity)
      (mul_le_mul_of_nonneg_left hpow (show 0 ≤ C * h ^ d by positivity)) 2
    convert h using 1 ; ring
  apply hraw.trans
  have hmain := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbpow (show 0 ≤ (3 : ℝ) ^ (d + 3) by positivity)) hμ
  dsimp only [σ] at hmain
  rw [output_recovery_power hL0.le] at hmain
  nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hh.le (2 * d))
    (Real.rpow_nonneg hL0.le ((gaussianDerivativeOrder d : ℝ) + d))) hμ]

end OAI.Analysis.PDE.Concentration
