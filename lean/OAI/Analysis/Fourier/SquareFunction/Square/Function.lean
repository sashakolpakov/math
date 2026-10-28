import OAI.Analysis.Fourier.SquareFunction.Pointwise
import OAI.Analysis.Fourier.SquareFunction.Scaling

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

theorem radiusDerivative_scaled {n : ℕ} (α r : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.SquareFunction.radiusDerivative α ((2 * Real.pi) * r) f x =
      radiusDerivativeCycles α r f x := by
  rw [OAI.Analysis.Fourier.SquareFunction.radiusDerivative, OAI.Analysis.Fourier.Wave.angularInverse_eq_fourierInv_scaled]
  unfold radiusDerivativeCycles
  apply congrArg (fun g : Space n → ℂ => 𝓕⁻ g x)
  funext ξ
  rw [OAI.Analysis.Fourier.Wave.angularFourier_scaled]
  have hm : OAI.Analysis.Fourier.SquareFunction.radiusDerivativeSymbol α ((2 * Real.pi) * r)
      ((2 * Real.pi) • ξ) = radiusMultiplier α ‖ξ‖ r := by
    change radiusMultiplier α ‖(2 * Real.pi) • ξ‖ ((2 * Real.pi) * r) = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact radiusMultiplier_scale (by positivity) α ‖ξ‖ r
  rw [hm]
  rfl

theorem steinSquareFunction_eq_cycles {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x =
      (∫⁻ r in Ioi 0, ‖radiusDerivativeCycles α r f x‖ₑ ^ 2 /
        ENNReal.ofReal r) ^ (1 / 2 : ℝ) := by
  unfold OAI.Analysis.Fourier.SquareFunction.steinSquareFunction
  rw [← radius_log_measure_scaling
    (fun r => ‖OAI.Analysis.Fourier.SquareFunction.radiusDerivative α r f x‖ₑ ^ 2)
    (by positivity : 0 < 2 * Real.pi)]
  simp_rw [radiusDerivative_scaled]

theorem measurable_steinSquareFunction {n : ℕ} (α : ℝ)
    (f : SchwartzMap (Space n) ℂ) :
    Measurable (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) := by
  have hm : Measurable (fun z : Space n × ℝ =>
      ‖radiusDerivativeCycles α z.2 f z.1‖ₑ ^ 2 / ENNReal.ofReal z.2) := by
    exact (((measurable_radiusDerivativeCycles α f).comp measurable_swap).enorm.pow_const
      (2 : ℕ)).div (ENNReal.measurable_ofReal.comp measurable_snd)
  have hi := hm.lintegral_prod_right' (ν := volume.restrict (Ioi 0))
  rw [show OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f =
    (fun x => (∫⁻ r in Ioi 0, ‖radiusDerivativeCycles α r f x‖ₑ ^ 2 /
      ENNReal.ofReal r) ^ (1 / 2 : ℝ)) from funext (steinSquareFunction_eq_cycles α f)]
  exact hi.pow_const _

/-- Exact `L²` identity for the manuscript's pointwise Stein square function. -/
theorem steinSquareFunction_integral_sq {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    (∫⁻ x : Space n, OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x ^ (2 : ℝ)) =
      ENNReal.ofReal (α / (2 * α - 1) * ‖f.toLp 2 volume‖ ^ 2) := by
  simp_rw [steinSquareFunction_eq_cycles, ← ENNReal.rpow_mul]
  norm_num
  exact radiusDerivativeCycles_total_energy hα f

theorem memLp_steinSquareFunction {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    MemLp (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) 2 volume := by
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    (measurable_steinSquareFunction α f).aestronglyMeasurable).2
  simpa only [ENNReal.toReal_ofNat, enorm_eq_self, steinSquareFunction_integral_sq hα f]
    using (ENNReal.ofReal_lt_top :
      ENNReal.ofReal (α / (2 * α - 1) * ‖f.toLp 2 volume‖ ^ 2) < ∞)

theorem eLpNorm_steinSquareFunction {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) 2 volume =
      ENNReal.ofReal (Real.sqrt (α / (2 * α - 1))) * eLpNorm f 2 volume := by
  have hc : 0 ≤ α / (2 * α - 1) := div_nonneg (by linarith) (by linarith)
  have hnorm : ENNReal.ofReal ‖f.toLp 2 volume‖ = eLpNorm f 2 volume := by
    rw [SchwartzMap.norm_toLp, ENNReal.ofReal_toReal (f.memLp 2 volume).ne]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (measurable_steinSquareFunction α f).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  rw [steinSquareFunction_integral_sq hα f,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hc (sq_nonneg _)) (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hc, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _), ENNReal.ofReal_mul (Real.sqrt_nonneg _), hnorm]

/-- The full `p = 2` square-function estimate, with the sharp constant and no
local-smoothing hypothesis, in every positive Euclidean dimension. -/
theorem steinSquareFunction_L2 {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) 2 volume ∧
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) 2 volume ≤
        ENNReal.ofReal C * eLpNorm f 2 volume := by
  refine ⟨Real.sqrt (α / (2 * α - 1)), Real.sqrt_pos.2 ?_, ?_⟩
  · exact div_pos (by linarith) (by linarith)
  · intro f
    exact ⟨memLp_steinSquareFunction hα f, (eLpNorm_steinSquareFunction hα f).le⟩

end OAI.Analysis.Fourier.SquareFunction
