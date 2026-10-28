import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

noncomputable section
open Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A quantitative Hölder remainder gives the actual Fréchet derivative.
This is used to identify the jets of the regularized boundary lift on the
hyperplane, where the regularization scale vanishes. -/
theorem hasFDerivAt_of_holder_remainder
    (f : E → F) (L : E →L[ℝ] F) (x : E) {C α : ℝ} (hα : 0 < α)
    (hbound : ∀ᶠ y in 𝓝 x,
      ‖f y - f x - L (y - x)‖ ≤ C * ‖y - x‖ ^ (1 + α)) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_tendsto]
  have hmajor : ∀ᶠ y in 𝓝 x,
      ‖y - x‖⁻¹ * ‖f y - f x - L (y - x)‖ ≤ C * ‖y - x‖ ^ α := by
    filter_upwards [hbound] with y hy
    by_cases he : y = x
    · subst y
      simp [Real.zero_rpow hα.ne']
    · have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
      calc
        _ ≤ ‖y - x‖⁻¹ * (C * ‖y - x‖ ^ (1 + α)) :=
          mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hn.le)
        _ = C * ‖y - x‖ ^ α := by
          rw [Real.rpow_add hn, Real.rpow_one]
          field_simp
  have ht : Tendsto (fun y : E ↦ C * ‖y - x‖ ^ α) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : E ↦ C * ‖y - x‖ ^ α) :=
      continuous_const.mul
        ((continuous_id.sub continuous_const).norm.rpow_const (fun _ ↦ Or.inr hα.le))
    simpa only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] using hc.tendsto x
  exact squeeze_zero' (Filter.Eventually.of_forall (fun y ↦ mul_nonneg
    (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))) hmajor ht

end OAI.Analysis.PDE.Schauder
