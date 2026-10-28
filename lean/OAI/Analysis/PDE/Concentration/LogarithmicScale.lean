import OAI.Analysis.PDE.Concentration.NormalizedPacket

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology

def packetLogScale (D h : ℝ) : ℝ := D * (1 + Real.log h⁻¹)

theorem exists_packet_log_scale (L₀ B : ℝ) :
    ∃ D h₀ : ℝ, 1 ≤ D ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      L₀ ≤ packetLogScale D h ∧ B * Real.log h⁻¹ ≤ packetLogScale D h ∧
        4 * (h * packetLogScale D h) ≤ 1 := by
  let D := max 1 (max L₀ B)
  have hD : 1 ≤ D := le_max_left _ _
  have hDL : L₀ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hDB : B ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hc : Continuous (fun h : ℝ => 4 * D * (h - h * Real.log h)) :=
    continuous_const.mul (continuous_id.sub Real.continuous_mul_log)
  have hn : ∀ᶠ h : ℝ in 𝓝 0, 4 * D * (h - h * Real.log h) < 1 :=
    hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨D, min 1 (δ / 2), hD, lt_min zero_lt_one (by positivity), min_le_left _ _, ?_⟩
  intro h hh hsmall
  have hh1 : h ≤ 1 := hsmall.trans (min_le_left _ _)
  have hlog : 0 ≤ Real.log h⁻¹ := Real.log_nonneg ((one_le_inv₀ hh).mpr hh1)
  have hT : 1 ≤ 1 + Real.log h⁻¹ := by linarith
  have hbase : D ≤ packetLogScale D h := by
    exact le_mul_of_one_le_right (zero_le_one.trans hD) hT
  refine ⟨hDL.trans hbase, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_right hDB hlog
    dsimp only [packetLogScale]
    nlinarith
  · have hnear : dist h 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh]
      have hs := hsmall.trans (min_le_right 1 (δ / 2))
      linarith
    have hv := (hb hnear).le
    simpa only [packetLogScale, Real.log_inv, sub_eq_add_neg] using (show 4 * (h * (D * (1 - Real.log h))) ≤ 1 by
      nlinarith [hv])

theorem cylinder_log_le_scale_log {h L : ℝ} (hh : 0 < h) (hL : 1 ≤ L)
    (ha : 4 * (h * L) ≤ 1) :
    1 + |Real.log (2 * (h * L))| ≤ 1 + Real.log h⁻¹ := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have harg : 0 < 2 * (h * L) := by positivity
  have hlog := Real.log_nonpos harg.le (by linarith : 2 * (h * L) ≤ 1)
  rw [abs_of_nonpos hlog, Real.log_inv]
  have hharg : h ≤ 2 * (h * L) := by nlinarith
  linarith [Real.log_le_log hh hharg]

theorem cancel_weighted_scales {c C Q h L u v W E : ℝ}
    (hc : 0 < c) (hh : 0 < h) (hL : 0 < L)
    (hb : c * h ^ 2 * L ^ v * W ≤ C * Q * (h ^ 2 * L ^ u * E)) :
    W ≤ (C / c) * Q * L ^ (u - v) * E := by
  have hp : 0 < c * h ^ 2 * L ^ v := by positivity
  have he : C * Q * (h ^ 2 * L ^ u * E) =
      (c * h ^ 2 * L ^ v) * ((C / c) * Q * L ^ (u - v) * E) := by
    rw [Real.rpow_sub hL]
    field_simp
  rw [he] at hb
  nlinarith

theorem packet_scale_exponent (n : ℕ) :
    ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) -
      (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) * (gaussianDerivativeOrder (n + 1) : ℝ)) =
      3 * ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 1) := by
  unfold gaussianDerivativeOrder
  push_cast
  field_simp
  ring

theorem packet_log_exponent (n : ℕ) :
    3 * ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 1) + 3 =
      (2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) * (3 * ((n : ℝ) + 5) / 2) := by
  field_simp
  ring

theorem packet_log_scale_bound (n : ℕ) {c C D h W E : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 1 ≤ D) (hh : 0 < h) (hh1 : h ≤ 1) (hE : 0 ≤ E)
    (ha : 4 * (h * packetLogScale D h) ≤ 1)
    (hb : c * h ^ 2 * (packetLogScale D h) ^
        (1 - (((n : ℝ) + 2) / ((n : ℝ) + 1)) * (gaussianDerivativeOrder (n + 1) : ℝ)) * W ≤
      C * (1 + |Real.log (2 * (h * packetLogScale D h))|) ^ 3 *
        (h ^ 2 * (packetLogScale D h) ^
          ((n : ℝ) + 4 + (gaussianDerivativeOrder (n + 1) : ℝ) / (n + 1)) * E)) :
    W ≤ ((C / c) * D ^ (3 * ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 1))) *
      (1 + Real.log h⁻¹) ^ ((2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))) * (3 * ((n : ℝ) + 5) / 2)) * E := by
  have hlog : 0 ≤ Real.log h⁻¹ := Real.log_nonneg ((one_le_inv₀ hh).mpr hh1)
  have hT : 0 < 1 + Real.log h⁻¹ := by positivity
  have hL1 : 1 ≤ packetLogScale D h := hD.trans
    (le_mul_of_one_le_right (zero_le_one.trans hD) (by linarith))
  have hL : 0 < packetLogScale D h := zero_lt_one.trans_le hL1
  have hbound := cancel_weighted_scales hc hh hL hb
  rw [packet_scale_exponent] at hbound
  have hlog3 := pow_le_pow_left₀ (by positivity) (cylinder_log_le_scale_log hh hL1 ha) 3
  apply hbound.trans
  calc
    _ ≤ (C / c) * (1 + Real.log h⁻¹) ^ 3 *
        (packetLogScale D h) ^ (3 * ((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 1)) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
      exact mul_le_mul_of_nonneg_left hlog3 (div_nonneg hC hc.le)
    _ = _ := by
      rw [packetLogScale, Real.mul_rpow (zero_le_one.trans hD) hT.le]
      rw [← packet_log_exponent, Real.rpow_add hT]
      simp only [Real.rpow_ofNat]
      ring

end OAI.Analysis.PDE.Concentration
