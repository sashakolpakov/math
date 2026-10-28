import Mathlib

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Filter
open scoped Topology

theorem rpow_add_one_upper {x : ℝ} (hx : 1 ≤ x) (b : ℝ) :
    (1+x)^b ≤ 2^(max b 0)*x^b := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  by_cases hb : 0 ≤ b
  · rw [max_eq_left hb]
    calc
      _ ≤ (2*x)^b := Real.rpow_le_rpow (by positivity) (by linarith) hb
      _ = _ := Real.mul_rpow (by norm_num) hx0.le
  · rw [max_eq_right (le_of_not_ge hb),Real.rpow_zero,one_mul]
    exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (le_of_not_ge hb)

theorem shifted_rpow_necessary {c D a b r : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (ha : 0 < a)
    (h : ∀ᶠ x : ℝ in atTop, c*(x+r)^a ≤ D*(1+x)^b) : a ≤ b := by
  by_contra hab
  have hba : b-a < 0 := by linarith
  have hl : ∀ᶠ x : ℝ in atTop,
      c*(1/2:ℝ)^a ≤ (D*2^(max b 0))*x^(b-a) := by
    filter_upwards [h,eventually_ge_atTop (max 1 (-2*r))] with x h hx
    have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
    have hxr : -2*r ≤ x := (le_max_right _ _).trans hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hlo : c*((1/2:ℝ)*x)^a ≤ c*(x+r)^a :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) ha.le) hc.le
    have hhi := mul_le_mul_of_nonneg_left (rpow_add_one_upper hx1 b) hD
    have hall := hlo.trans (h.trans hhi)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 1/2) hx0.le] at hall
    have hm := mul_le_mul_of_nonneg_right hall (Real.rpow_nonneg hx0.le (-a))
    have hcancel : x^a*x^(-a) = 1 := by rw [←Real.rpow_add hx0]; simp
    have hp : x^b*x^(-a) = x^(b-a) := by rw [←Real.rpow_add hx0]; rfl
    calc
      c*(1/2:ℝ)^a = (c*((1/2:ℝ)^a*x^a))*x^(-a) := by rw [mul_assoc, mul_assoc,hcancel,mul_one]
      _ ≤ (D*(2^(max b 0)*x^b))*x^(-a) := hm
      _ = _ := by rw [mul_assoc,mul_assoc,hp]; ring
  have ht : Tendsto (fun x : ℝ => (D*2^(max b 0))*x^(b-a)) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => x^(b-a)) atTop (𝓝 0) := by
      simpa only [neg_sub] using tendsto_rpow_neg_atTop (show 0 < a-b by linarith)
    simpa only [mul_zero] using hh.const_mul (D*2^(max b 0))
  have hz := ge_of_tendsto ht hl
  have hp : 0 < c*(1/2:ℝ)^a := by positivity
  linarith

theorem shifted_log_power_necessary {c D a b K : ℝ} (hc : 0 < c) (hD : 0 ≤ D)
    (ha : 0 < a) (hK : 0 < K)
    (h : ∀ᶠ N : ℝ in atTop,
      c*(Real.log (N/K))^a ≤ D*(1+Real.log (N/4))^b) : a ≤ b := by
  have ht : Tendsto (fun x : ℝ => 4*Real.exp x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Real.tendsto_exp_atTop
  apply shifted_rpow_necessary (r := Real.log 4-Real.log K) hc hD ha
  filter_upwards [ht.eventually h] with x hx
  have hl : Real.log (4*Real.exp x/K) = x+(Real.log 4-Real.log K) := by
    rw [Real.log_div (by positivity) hK.ne',Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp]
    ring
  have hr : Real.log (4*Real.exp x/4) = x := by
    rw [show 4*Real.exp x/4 = Real.exp x by ring,Real.log_exp]
  simpa only [hl,hr] using hx

theorem log_quotient_ge_half {K N : ℝ} (hK : 1 ≤ K) (hN : K^2 ≤ N) :
    (1/2:ℝ)*Real.log N ≤ Real.log (N/K) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hN0 : 0 < N := (sq_pos_of_pos hK0).trans_le hN
  have hh := Real.log_le_log (sq_pos_of_pos hK0) hN
  rw [Real.log_pow] at hh
  rw [Real.log_div hN0.ne' hK0.ne']
  norm_num at hh
  linarith

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
