import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Frequency Cutoff -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FrequencyCutoff.CM.Construction

noncomputable section

/-! Smooth frequency cutoffs and quantitative high-frequency control. -/

open FourierTransform TemperedDistribution _root_.MeasureTheory ENNReal
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A genuine smooth cutoff equal to one through radius R and zero beyond radius 2R. -/
def frequencyCutoff {R : ℝ} (hR : 0 < R) : ContDiffBump (0 : E) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by linarith

theorem frequencyCutoff_temperate {R : ℝ} (hR : 0 < R) :
    (fun x : E => (frequencyCutoff (E := E) hR x : ℂ)).HasTemperateGrowth := by
  have h := (frequencyCutoff (E := E) hR).hasCompactSupport.hasTemperateGrowth
    (frequencyCutoff (E := E) hR).contDiff
  fun_prop

theorem frequencyCutoff_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    frequencyCutoff (E := E) hR x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, dist_zero_right, frequencyCutoff] using hx

/-- The discarded frequencies gain one inverse power of the cutoff radius. -/
theorem frequencyCutoff_tailSymbol_bound {R : ℝ} (hR : 0 < R) (x : E) :
    ‖((1 - frequencyCutoff (E := E) hR x : ℝ) : ℂ) *
      (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ R⁻¹ := by
  by_cases hx : ‖x‖ ≤ R
  · rw [frequencyCutoff_eq_one hR hx]
    simp only [sub_self, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity
  · have hxR : R ≤ ‖x‖ := (lt_of_not_ge hx).le
    have hs : R ≤ Real.sqrt (1 + ‖x‖ ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [sq_nonneg (‖x‖ - R)]
    have hpow : (1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) =
        (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
        Real.sqrt_eq_rpow]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (frequencyCutoff (E := E) hR).le_one),
      abs_of_nonneg (by positivity), hpow]
    calc
      (1 - frequencyCutoff (E := E) hR x) * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ ≤
          1 * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹ := by
        apply mul_le_mul_of_nonneg_right
        · linarith [(frequencyCutoff (E := E) hR).nonneg' x]
        · positivity
      _ ≤ R⁻¹ := by simpa only [one_mul] using inv_anti₀ hR hs

variable {F : Type*} [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem fourierMultiplier_sub {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g - h) u =
      fourierMultiplierCLM F g u - fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_sub hg hh,
    sub_apply]
  exact (fourierInvCLM ℂ 𝓢'(E, F)).map_sub _ _

/-- Removing bounded frequencies has an L² error uniformly controlled by the H¹ norm. -/
theorem frequencyCutoff_tail_l2_bound {R : ℝ} (hR : 0 < R)
    (u : Bounds.CM.Construction.sobolevDistributionSubmodule E F 1) :
    ∃ w : Lp F 2 (volume : Measure E),
      (w : 𝓢'(E, F)) = u.val -
        fourierMultiplierCLM F (fun x : E => (frequencyCutoff (E := E) hR x : ℂ)) u.val ∧
      ‖w‖ ≤ R⁻¹ * Bounds.CM.Construction.sobolevNorm E F 1 u := by
  obtain ⟨f, rfl⟩ := (Bounds.CM.Construction.sobolevCoordinateEquiv E F 1).surjective u
  let χ : E → ℂ := fun x => (frequencyCutoff (E := E) hR x : ℂ)
  let b : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (-1 / 2 : ℝ) : ℝ) : ℂ)
  have hχ : χ.HasTemperateGrowth := frequencyCutoff_temperate hR
  have hb : b.HasTemperateGrowth := by dsimp [b]; fun_prop
  have ht : (1 - χ).HasTemperateGrowth := by
    change (fun x => 1 - χ x).HasTemperateGrowth
    fun_prop
  obtain ⟨w, hw, hn⟩ := Bounds.CM.Construction.fourierMultiplier_l2_bound (ht.mul hb)
    (C := R⁻¹) (fun x => by
      simpa only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, χ, b, Complex.ofReal_sub,
        Complex.ofReal_one] using frequencyCutoff_tailSymbol_bound hR x) f
  refine ⟨w, ?_, ?_⟩
  · change (w : 𝓢'(E, F)) = besselPotential E F (-1) (f : 𝓢'(E, F)) -
      fourierMultiplierCLM F χ (besselPotential E F (-1) (f : 𝓢'(E, F)))
    have hsub := fourierMultiplier_sub (F := F) (g := 1) (h := χ)
      (by change (fun _ : E => (1 : ℂ)).HasTemperateGrowth; fun_prop)
      hχ (besselPotential E F (-1) (f : 𝓢'(E, F)))
    rw [show (1 : E → ℂ) = (fun _ => 1) from rfl,
      fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply] at hsub
    rw [← hsub]
    change (w : 𝓢'(E, F)) =
      fourierMultiplierCLM F (1 - χ) (fourierMultiplierCLM F b (f : 𝓢'(E, F)))
    rw [fourierMultiplierCLM_fourierMultiplierCLM_apply hb ht, hw]
    congr 2
    exact mul_comm _ _
  · simpa only [Bounds.CM.Construction.sobolevNorm, LinearEquiv.symm_apply_apply] using hn

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FrequencyCutoff.CM.Construction
