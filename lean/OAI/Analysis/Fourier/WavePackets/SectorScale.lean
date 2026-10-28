import OAI.Analysis.Fourier.WavePackets.AngularPartition
import OAI.Analysis.PDE.Concentration.LogarithmicScale

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration
open scoped Topology

def packetFrame {d : ℕ} (R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1)) :
    OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d :=
  (OAI.Analysis.PDE.Concentration.spatialFinIsometry d).trans (R.trans (OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm)

theorem scaled_orientedPeriodicFrequency_packetFrame {d : ℕ}
    (R : Space (d + 1) ≃ₗᵢ[ℝ] Space (d + 1)) (h : ℝ) (k : Fin (d + 1) → ℤ) :
    h • OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency (packetFrame R) k =
      (OAI.Analysis.PDE.Concentration.spatialFinIsometry d).symm (R (h • periodicFrequency k)) := by
  simp [OAI.Analysis.PDE.Concentration.orientedPeriodicFrequency, packetFrame]

def logarithmicSectorWidth (γ₀ L : ℝ) : ℝ := γ₀ / Real.sqrt L

theorem logarithmicSectorWidth_bounds {γ₀ L : ℝ} (hγ₀ : 0 < γ₀) (hL : 1 ≤ L) :
    0 < logarithmicSectorWidth γ₀ L ∧ logarithmicSectorWidth γ₀ L ≤ γ₀ := by
  have hs : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).mpr hL
  refine ⟨div_pos hγ₀ (lt_of_lt_of_le zero_lt_one hs), ?_⟩
  exact div_le_self hγ₀.le hs

theorem logarithmicSectorWidth_cancel {γ₀ L : ℝ} (hL : 0 < L) :
    Real.sqrt L * logarithmicSectorWidth γ₀ L = γ₀ := by
  exact mul_div_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr hL))

theorem logarithmicSectorWidth_count (d : ℕ) {γ₀ L : ℝ} (_ : 0 < γ₀) (hL : 0 < L) :
    ((logarithmicSectorWidth γ₀ L)⁻¹) ^ d = (γ₀⁻¹) ^ d * L ^ ((d : ℝ) / 2) := by
  rw [logarithmicSectorWidth, inv_div, div_eq_mul_inv, mul_pow, mul_comm]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  congr 1
  ring

theorem one_le_packetLogScale {D h : ℝ} (hD : 1 ≤ D) (hh : 0 < h) (hh1 : h ≤ 1) :
    1 ≤ OAI.Analysis.PDE.Concentration.packetLogScale D h := by
  have hl : 0 ≤ Real.log h⁻¹ := Real.log_nonneg ((one_le_inv₀ hh).mpr hh1)
  exact hD.trans (le_mul_of_one_le_right (zero_le_one.trans hD) (by linarith))

/-- Once the constant in the logarithmic scale has been fixed by the
sector estimate, the physical transverse radius is still small for all
sufficiently small `h`. -/
theorem exists_small_packetLogScale (D : ℝ) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      h * OAI.Analysis.PDE.Concentration.packetLogScale D h ≤ 1 / 4 := by
  have hc : Continuous (fun h : ℝ => 4 * D * (h - h * Real.log h)) :=
    continuous_const.mul (continuous_id.sub Real.continuous_mul_log)
  have hn : ∀ᶠ h : ℝ in 𝓝 0, 4 * D * (h - h * Real.log h) < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨min 1 (δ / 2), lt_min zero_lt_one (by positivity), min_le_left _ _, ?_⟩
  intro h hh hsmall
  have hnear : dist h 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hh]
    have hs := hsmall.trans (min_le_right 1 (δ / 2))
    linarith
  have hv := hb hnear
  simp only [OAI.Analysis.PDE.Concentration.packetLogScale, Real.log_inv]
  nlinarith

end OAI.Analysis.Fourier.WavePackets
