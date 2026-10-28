import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # Smooth -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth.CM.Construction

noncomputable section

section

/-! Smooth representatives from all integer Sobolev orders, through Fourier moments. -/

open _root_.MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap BoundedContinuousFunction ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem polynomial_inverse_weight_bound (n : ℕ) (x : E) :
    ‖x‖ ^ n * (1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) ≤ 1 := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, ← div_pow]
  apply pow_le_one₀ (by positivity)
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (‖x‖ - 1)]

/-- Sufficient Sobolev order gives an integrable polynomial moment of the actual Fourier L¹ density. -/
theorem sobolev_fourier_moment_integrable (n : ℕ) {s : ℝ}
    (hs : Module.finrank ℝ E < 2 * s) {u : 𝓢'(E, F)}
    (hu : MemSobolev (2 * (n : ℝ) + s) 2 u)
    (v : Lp F 1 (volume : Measure E)) (hv : 𝓕 u = (v : 𝓢'(E, F))) :
    Integrable (fun x : E => ‖x‖ ^ n * ‖v x‖) := by
  have hreg : MemSobolev s 2 (besselPotential E F (2 * (n : ℝ)) u) := by
    rw [memSobolev_besselPotential_iff]
    exact hu
  obtain ⟨w, hw⟩ := hreg.fourier_memL1 hs
  let g : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ)
  have hg : g.HasTemperateGrowth := by dsimp [g]; fun_prop
  have hgb : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    dsimp [g]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (neg_nonpos.mpr (Nat.cast_nonneg n))
  let G : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup g hg.1.continuous 1 hgb
  let m : Lp ℂ ⊤ (volume : Measure E) := G.memLp_top.toLp G
  have hd : smulLeftCLM F g (w : 𝓢'(E, F)) = (v : 𝓢'(E, F)) := by
    rw [← hw, fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      smulLeftCLM_smulLeftCLM_apply (by fun_prop) hg]
    have hsymbol : (fun x : E => (((1 + ‖x‖ ^ 2) ^ ((2 * (n : ℝ)) / 2) : ℝ) : ℂ)) * g =
        (fun _ : E => (1 : ℂ)) := by
      ext x
      change (((1 + ‖x‖ ^ 2) ^ ((2 * (n : ℝ)) / 2) : ℝ) : ℂ) *
        (((1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul]
      change Complex.ofReal
        ((1 + ‖x‖ ^ 2) ^ ((2 * (n : ℝ)) / 2) * (1 + ‖x‖ ^ 2) ^ (-(n : ℝ))) =
          Complex.ofReal 1
      apply congrArg Complex.ofReal
      rw [← Real.rpow_add (by positivity)]
      rw [show (2 * (n : ℝ)) / 2 + -(n : ℝ) = 0 by ring, Real.rpow_zero]
    rw [hsymbol, smulLeftCLM_const, one_smul, hv]
  have heq : v = m • w := by
    apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := F) (μ := (volume : Measure E)) (p := 1)))
    change (v : 𝓢'(E, F)) = ((m • w : Lp F 1 (volume : Measure E)) : 𝓢'(E, F))
    exact hd.symm.trans (Lp.toTemperedDistribution_smul_eq hg G.memLp_top w).symm
  apply (L1.integrable_coeFn w).norm.mono'
  · exact (by fun_prop : Continuous (fun x : E => ‖x‖ ^ n)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable v).norm
  · have hvcoe := Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) m w
    rw [← heq] at hvcoe
    filter_upwards [hvcoe, G.memLp_top.coeFn_toLp] with x hx hm
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hx]
    change ‖x‖ ^ n * ‖m x • w x‖ ≤ ‖w x‖
    rw [norm_smul, show m x = g x from hm]
    change ‖x‖ ^ n * (‖(((1 + ‖x‖ ^ 2) ^ (-(n : ℝ)) : ℝ) : ℂ)‖ * ‖w x‖) ≤ ‖w x‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_assoc]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (polynomial_inverse_weight_bound n x) (norm_nonneg (w x))

/-- A distribution lying in every integer Sobolev space has an actual smooth representative. -/
theorem sobolev_all_orders_smooth {u : 𝓢'(E, F)}
    (hu : ∀ n : ℕ, MemSobolev (n : ℝ) 2 u) :
    ∃ f : E →ᵇ F, SobolevInv.CM.Construction.boundedFunctionDistribution f = u ∧ ContDiff ℝ (⊤ : ℕ∞) (f : E → F) := by
  let d := Module.finrank ℝ E + 1
  have hd : Module.finrank ℝ E < 2 * (d : ℝ) := by
    dsimp [d]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)]
  obtain ⟨v, hv⟩ := (hu d).fourier_memL1 hd
  have hmoment : ∀ n : ℕ, Integrable (fun x : E => ‖x‖ ^ n * ‖v x‖) := by
    intro n
    apply sobolev_fourier_moment_integrable n hd _ v hv
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hu (2 * n + d)
  have hdiff : ContDiff ℝ (⊤ : ℕ∞) (𝓕 (v : E → F)) := Real.contDiff_fourier (fun n _ => hmoment n)
  refine ⟨Real.Lp.fourierTransformInv v, ?_, ?_⟩
  · rw [SobolevInv.CM.Construction.l1_fourierInv_distribution, ← hv, fourierInv_fourier_eq]
  · have heq : (Real.Lp.fourierTransformInv v : E → F) = (𝓕 (v : E → F)) ∘ Neg.neg := by
      ext x
      rw [Real.Lp.fourierTransformInv_apply, Real.fourierInv_eq_fourier_neg]
      rfl
    rw [heq]
    exact hdiff.comp contDiff_neg

end

section

/-! Equality of a continuous representative and an L2 function as
distributions implies equality almost everywhere of their actual values. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem boundedFunctionDistribution_eq_lp_ae (f : BoundedContinuousFunction E ℂ)
    (u : Lp ℂ 2 (volume : Measure E))
    (h : SobolevInv.CM.Construction.boundedFunctionDistribution f = (u : 𝓢'(E, ℂ))) :
    (f : E → ℂ) =ᵐ[volume] u := by
  apply ae_eq_of_integral_contDiff_smul_eq f.continuous.locallyIntegrable
    (Lp.memLp u |>.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
  intro g hg hgc
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have heq := congrArg (fun T : 𝓢'(E, ℂ) => T (hc.toSchwartzMap hs)) h
  rw [SobolevInv.CM.Construction.boundedFunctionDistribution_apply, Lp.toTemperedDistribution_apply] at heq
  change (∫ x, (g x : ℂ) • f x) = ∫ x, (g x : ℂ) • u x at heq
  simpa only [Complex.coe_smul] using heq

end

/-! Compact Schwartz tests detect a continuous function pointwise on an
open Euclidean domain. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem continuous_zero_of_schwartz_tests {U : Set E} (hU : IsOpen U)
    (f : E → ℂ) (hf : ContinuousOn f U)
    (ht : ∀ g : 𝓢(E, ℂ), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
      (∫ x, f x * g x) = 0) : EqOn f 0 U := by
  have hae : ∀ᵐ x, x ∈ U → f x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.locallyIntegrableOn hU.measurableSet)
    intro g hg hgc hgs
    have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    have hs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg
    have hts : tsupport (Complex.ofRealCLM ∘ g) = tsupport g := by
      apply congrArg closure
      ext x
      simp only [Function.mem_support, Function.comp_apply, Complex.ofRealCLM_apply]
      exact not_congr Complex.ofReal_eq_zero
    have h := ht (hc.toSchwartzMap hs) hc (hts ▸ hgs)
    change (∫ x, f x * (g x : ℂ)) = 0 at h
    simpa only [Complex.real_smul, mul_comm] using h
  apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hU hf continuousOn_const
  exact (ae_restrict_iff' hU.measurableSet).mpr hae

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth.CM.Construction
