import OAI.Analysis.Fourier.SquareFunction.Radius.Scalar
import Mathlib.MeasureTheory.Integral.Prod

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.Fourier.SquareFunction

def radiusPowerIntegral {n : ℕ} (α : ℝ) (g : Space n → ℂ) (r : ℝ) : ℂ :=
  ∫ ξ, radiusPower α ‖ξ‖ r • g ξ

def radiusPowerIntegralDerivative {n : ℕ} (α : ℝ) (g : Space n → ℂ) (r : ℝ) : ℂ :=
  ∫ ξ, radiusPowerDerivative α ‖ξ‖ r • g ξ

theorem measurable_radiusPowerDerivative (α : ℝ) :
    Measurable (fun p : ℝ × ℝ => radiusPowerDerivative α p.1 p.2) :=
  measurable_snd.inv.mul (measurable_radiusMultiplier α)

theorem integrable_radiusPower_mul {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {g : Space n → ℂ} (hg : Integrable g) (r : ℝ) :
    Integrable (fun ξ => radiusPower α ‖ξ‖ r • g ξ) := by
  refine hg.norm.mono' ?_ ?_
  · have hm : Measurable (fun ξ : Space n => radiusPower α ‖ξ‖ r) := by
      unfold radiusPower
      fun_prop
    exact hm.aestronglyMeasurable.smul hg.aestronglyMeasurable
  · filter_upwards [] with ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radiusPower_nonneg _ _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (radiusPower_le_one hα _ _)

theorem radiusPowerDerivative_integral_norm {α ρ a b : ℝ}
    (hα : 0 < α) (hρ : 0 ≤ ρ) (ha : 0 < a) (hab : a ≤ b) (z : ℂ) :
    (∫ r in Ioc a b, ‖radiusPowerDerivative α ρ r • z‖) =
      (radiusPower α ρ b - radiusPower α ρ a) * ‖z‖ := by
  have he : (∫ r in Ioc a b, ‖radiusPowerDerivative α ρ r • z‖) =
      ∫ r in Ioc a b, radiusPowerDerivative α ρ r * ‖z‖ := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
      (radiusPowerDerivative_nonneg hα.le hρ (ha.trans hr.1))]
  rw [he, integral_mul_const, ← intervalIntegral.integral_of_le hab,
    (radiusPower_intervalIntegral hα hρ ha hab).2]

theorem integrable_radiusPowerDerivative_prod {n : ℕ} {α a b : ℝ}
    (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b)
    {g : Space n → ℂ} (hg : Integrable g) :
    Integrable (fun p : Space n × ℝ => radiusPowerDerivative α ‖p.1‖ p.2 • g p.1)
      (volume.prod (volume.restrict (Ioc a b))) := by
  have hm : AEStronglyMeasurable
      (fun p : Space n × ℝ => radiusPowerDerivative α ‖p.1‖ p.2 • g p.1)
      (volume.prod (volume.restrict (Ioc a b))) := by
    exact ((measurable_radiusPowerDerivative α).comp
      (continuous_fst.norm.measurable.prodMk measurable_snd)).aestronglyMeasurable.smul
      hg.aestronglyMeasurable.comp_fst
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [] with ξ
    exact ((radiusPower_intervalIntegral hα (norm_nonneg ξ) ha hab).1.1).smul_const (g ξ)
  · refine hg.norm.mono' ?_ ?_
    · exact hm.norm.integral_prod_right'
    · filter_upwards [] with ξ
      rw [radiusPowerDerivative_integral_norm hα (norm_nonneg ξ) ha hab]
      have hnonneg : 0 ≤ ∫ r in Ioc a b, ‖radiusPowerDerivative α ‖ξ‖ r • g ξ‖ :=
        integral_nonneg (fun _ => norm_nonneg _)
      rw [radiusPowerDerivative_integral_norm hα (norm_nonneg ξ) ha hab] at hnonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      apply mul_le_of_le_one_left (norm_nonneg _)
      linarith [radiusPower_le_one hα.le ‖ξ‖ b, radiusPower_nonneg α ‖ξ‖ a]

theorem radiusPowerIntegral_sub {n : ℕ} {α a b : ℝ}
    (hα : 0 < α) (ha : 0 < a) (hab : a ≤ b)
    {g : Space n → ℂ} (hg : Integrable g) :
    radiusPowerIntegral α g b - radiusPowerIntegral α g a =
      ∫ r in a..b, radiusPowerIntegralDerivative α g r := by
  rw [radiusPowerIntegral, radiusPowerIntegral,
    ← integral_sub (integrable_radiusPower_mul hα.le hg b) (integrable_radiusPower_mul hα.le hg a)]
  have he : (fun ξ : Space n => radiusPower α ‖ξ‖ b • g ξ - radiusPower α ‖ξ‖ a • g ξ) =
      fun ξ => ∫ r in Ioc a b, radiusPowerDerivative α ‖ξ‖ r • g ξ := by
    funext ξ
    rw [integral_smul_const, ← intervalIntegral.integral_of_le hab,
      (radiusPower_intervalIntegral hα (norm_nonneg ξ) ha hab).2, sub_smul]
  rw [he, integral_integral_swap (integrable_radiusPowerDerivative_prod hα ha hab hg),
    ← intervalIntegral.integral_of_le hab]
  rfl

theorem hasDerivAt_radiusPowerIntegral_of_continuousDerivative {n : ℕ} {α r : ℝ}
    (hα : 0 < α) (hr : 0 < r) {g : Space n → ℂ} (hg : Integrable g)
    (hc : ContinuousOn (radiusPowerIntegralDerivative α g) (Ioi 0)) :
    HasDerivAt (radiusPowerIntegral α g) (radiusPowerIntegralDerivative α g r) r := by
  let a : ℝ := r / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have har : a < r := by dsimp [a]; linarith
  have hi : IntervalIntegrable (radiusPowerIntegralDerivative α g) volume a r := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro s hs
    have hs' : s ∈ Icc a r := by simpa only [uIcc_of_le har.le] using hs
    exact lt_of_lt_of_le ha hs'.1
  have hd := (intervalIntegral.integral_hasStrictDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc r hr)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hr))).hasDerivAt
  have he : radiusPowerIntegral α g =ᶠ[𝓝 r]
      (fun s => radiusPowerIntegral α g a + ∫ t in a..s, radiusPowerIntegralDerivative α g t) := by
    filter_upwards [lt_mem_nhds har] with s hs
    exact (sub_eq_iff_eq_add.mp (radiusPowerIntegral_sub hα ha hs.le hg)).trans (add_comm _ _)
  exact (hd.const_add (radiusPowerIntegral α g a)).congr_of_eventuallyEq he

end OAI.Analysis.Fourier.SquareFunction
