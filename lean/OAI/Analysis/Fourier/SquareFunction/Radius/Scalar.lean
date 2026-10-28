import OAI.Analysis.Fourier.SquareFunction.Multiplier
import OAI.Analysis.Fourier.SquareFunction.Scaling
import OAI.Analysis.Fourier.Estimates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.Fourier.SquareFunction

def radiusPower (α ρ r : ℝ) : ℝ := (max (1 - (ρ / r) ^ 2) 0) ^ α

def radiusPowerDerivative (α ρ r : ℝ) : ℝ := r⁻¹ * radiusMultiplier α ρ r

theorem radiusPower_nonneg (α ρ r : ℝ) : 0 ≤ radiusPower α ρ r :=
  Real.rpow_nonneg (le_max_right _ _) _

theorem radiusPower_le_one {α : ℝ} (hα : 0 ≤ α) (ρ r : ℝ) :
    radiusPower α ρ r ≤ 1 := by
  apply Real.rpow_le_one (le_max_right _ _) _ hα
  exact max_le (by nlinarith [sq_nonneg (ρ / r)]) zero_le_one

theorem radiusPower_continuousOn {α : ℝ} (hα : 0 < α) (ρ : ℝ) :
    ContinuousOn (radiusPower α ρ) (Ioi 0) := by
  intro r hr
  have hc : ContinuousAt (fun r : ℝ => max (1 - (ρ / r) ^ 2) 0) r :=
    (continuousAt_const.sub ((continuousAt_const.div continuousAt_id
      (ne_of_gt hr)).pow 2)).max continuousAt_const
  exact ((Real.continuous_rpow_const hα.le).continuousAt.comp hc).continuousWithinAt

theorem radiusPower_zero {α ρ r : ℝ} (hα : 0 < α) (hr : 0 < r) (hρr : r ≤ ρ) :
    radiusPower α ρ r = 0 := by
  have h : 1 ≤ ρ / r := (le_div_iff₀ hr).mpr (by simpa using hρr)
  have hb : 1 - (ρ / r) ^ 2 ≤ 0 := by nlinarith
  simp [radiusPower, max_eq_right hb, Real.zero_rpow hα.ne']

theorem radiusPower_hasDerivAt {α ρ r : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r) :
    HasDerivAt (radiusPower α ρ) (radiusPowerDerivative α ρ r) r := by
  have hr : 0 < r := lt_of_le_of_lt hρ hρr
  have hb : 0 < 1 - ρ ^ 2 / r ^ 2 := by
    have hh : ρ ^ 2 / r ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hr)).mpr (by nlinarith)
    linarith
  have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hd := ((hasDerivAt_const r (1 : ℝ)).sub
    ((hasDerivAt_const r (ρ ^ 2)).div hp (pow_ne_zero 2 hr.ne'))).rpow_const
      (p := α) (Or.inl hb.ne')
  simp only [Pi.sub_apply, Pi.div_apply] at hd
  have he : radiusPower α ρ =ᶠ[𝓝 r] (fun s : ℝ => (1 - ρ ^ 2 / s ^ 2) ^ α) := by
    have hc : ContinuousAt (fun s : ℝ => 1 - ρ ^ 2 / s ^ 2) r :=
      continuousAt_const.sub (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hr.ne'))
    filter_upwards [hc.eventually (lt_mem_nhds hb)] with s hs
    simp only [radiusPower, div_pow, max_eq_left hs.le]
  apply HasDerivAt.congr_of_eventuallyEq _ he
  convert hd using 1
  simp only [radiusPowerDerivative, radiusMultiplier, ite_eq_left hρr]
  field_simp [hr.ne']
  ; ring

theorem radiusPowerDerivative_nonneg {α ρ r : ℝ} (hα : 0 ≤ α) (hρ : 0 ≤ ρ) (hr : 0 < r) :
    0 ≤ radiusPowerDerivative α ρ r := by
  unfold radiusPowerDerivative radiusMultiplier
  split_ifs with h
  · have hb : 0 ≤ 1 - ρ ^ 2 / r ^ 2 := by
      have hh : ρ ^ 2 / r ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hr)).mpr (by nlinarith)
      linarith
    exact mul_nonneg (inv_nonneg.mpr hr.le) (mul_nonneg (by positivity) (Real.rpow_nonneg hb _))
  · simp

theorem radiusPower_intervalIntegral_above {α ρ a b : ℝ}
    (hα : 0 < α) (hρ : 0 ≤ ρ) (ha : 0 < a) (hρa : ρ ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (radiusPowerDerivative α ρ) volume a b ∧
      (∫ r in a..b, radiusPowerDerivative α ρ r) = radiusPower α ρ b - radiusPower α ρ a := by
  have hc : ContinuousOn (radiusPower α ρ) (Icc a b) :=
    (radiusPower_continuousOn hα ρ).mono (fun x hx => lt_of_lt_of_le ha hx.1)
  have hd : ∀ x ∈ Ioo a b, HasDerivAt (radiusPower α ρ) (radiusPowerDerivative α ρ x) x :=
    fun x hx => radiusPower_hasDerivAt hρ (lt_of_le_of_lt hρa hx.1)
  have hi : IntervalIntegrable (radiusPowerDerivative α ρ) volume a b := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    · simpa only [uIcc_of_le hab] using hc
    · simpa only [min_eq_left hab, max_eq_right hab] using hd
    · intro x hx
      exact radiusPowerDerivative_nonneg hα.le hρ (lt_of_lt_of_le ha (by simpa only [min_eq_left hab] using hx.1.le))
  exact ⟨hi, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hc hd hi⟩

theorem radiusPower_intervalIntegral_below {α ρ a b : ℝ}
    (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b) (hbρ : b ≤ ρ) :
    IntervalIntegrable (radiusPowerDerivative α ρ) volume a b ∧
      (∫ r in a..b, radiusPowerDerivative α ρ r) = radiusPower α ρ b - radiusPower α ρ a := by
  have he : EqOn (radiusPowerDerivative α ρ) (fun _ => (0 : ℝ)) (uIcc a b) := by
    intro x hx
    have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hx
    simp only [radiusPowerDerivative, radiusMultiplier, ite_eq_right (not_lt.mpr (hx'.2.trans hbρ)), mul_zero]
  have hi : IntervalIntegrable (radiusPowerDerivative α ρ) volume a b :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b).congr_uIoo
      (fun x hx => (he (Ioo_subset_Icc_self hx)).symm)
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_congr he, intervalIntegral.integral_zero,
    radiusPower_zero hα (lt_of_lt_of_le ha hab) hbρ, radiusPower_zero hα ha (hab.trans hbρ)]
  simp

/-- FTC remains valid across the singular moving boundary for every positive
Bochner--Riesz exponent. Nonnegativity supplies integrability at that boundary. -/
theorem radiusPower_intervalIntegral {α ρ a b : ℝ}
    (hα : 0 < α) (hρ : 0 ≤ ρ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (radiusPowerDerivative α ρ) volume a b ∧
      (∫ r in a..b, radiusPowerDerivative α ρ r) = radiusPower α ρ b - radiusPower α ρ a := by
  by_cases hρa : ρ ≤ a
  · exact radiusPower_intervalIntegral_above hα hρ ha hρa hab
  by_cases hbρ : b ≤ ρ
  · exact radiusPower_intervalIntegral_below hα ha hab hbρ
  have haρ : a < ρ := lt_of_not_ge hρa
  have hρb : ρ < b := lt_of_not_ge hbρ
  obtain ⟨hi₁, he₁⟩ := radiusPower_intervalIntegral_below hα ha haρ.le le_rfl
  obtain ⟨hi₂, he₂⟩ := radiusPower_intervalIntegral_above hα hρ (ha.trans haρ) le_rfl hρb.le
  refine ⟨hi₁.trans hi₂, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂, he₁, he₂]
  ring

end OAI.Analysis.Fourier.SquareFunction
