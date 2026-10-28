import OAI.Analysis.Fourier.Restriction.Geometry

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem packetCap_subset_nearby_ball {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    {x : Space n} (hx : |‖x‖ - 1| ≤ δ) :
    OAI.MeasureTheory.Kakeya.packetCap δ (‖x‖⁻¹ • x) ⊆ ball x (2 * δ) := by
  have hx0 : 0 < ‖x‖ := by have := (abs_le.mp hx).1; linarith
  let u := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0), inv_mul_cancel₀ hx0.ne']
  have hxu : x = ‖x‖ • u := by simp [u, smul_smul, hx0.ne']
  have hdist : dist u x = |‖x‖ - 1| := by
    rw [dist_eq_norm]
    nth_rw 1 [hxu]
    rw [show u - ‖x‖ • u = (1 - ‖x‖) • u by simp [sub_smul], norm_smul, hu,
      mul_one, Real.norm_eq_abs, abs_sub_comm]
  intro ω hω
  rw [mem_ball]
  have hcap : dist ω u ≤ δ / 32 := by simpa only [dist_eq_norm] using hω.2
  calc
    dist ω x ≤ dist ω u + dist u x := dist_triangle _ _ _
    _ ≤ δ / 32 + δ := add_le_add hcap (by simpa only [hdist] using hx)
    _ < 2 * δ := by linarith

theorem sphere_neighborhood_mass_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ x : Space n,
      |‖x‖ - 1| ≤ δ → ENNReal.ofReal (c * δ ^ (n - 1)) ≤ OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball x (2 * δ)) := by
  obtain ⟨c, C, hc, hC, H⟩ := packetCap_real_comparable hn
  refine ⟨c, hc, ?_⟩
  intro δ hδ hδhalf x hx
  have hx0 : 0 < ‖x‖ := by have := (abs_le.mp hx).1; linarith
  have hu : ‖‖x‖⁻¹ • x‖ = 1 := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0), inv_mul_cancel₀ hx0.ne']
  have HL := (H δ (‖x‖⁻¹ • x) hδ (by linarith) hu).1
  calc
    _ ≤ ENNReal.ofReal ((OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (OAI.MeasureTheory.Kakeya.packetCap δ (‖x‖⁻¹ • x))) :=
      ENNReal.ofReal_le_ofReal HL
    _ = OAI.Analysis.Fourier.Restriction.sphereMeasure n (OAI.MeasureTheory.Kakeya.packetCap δ (‖x‖⁻¹ • x)) := by
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ _ := measure_mono (packetCap_subset_nearby_ball hδ hδhalf hx)

end OAI.Analysis.Fourier.Restriction
