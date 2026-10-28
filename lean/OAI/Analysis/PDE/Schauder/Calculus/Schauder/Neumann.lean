import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! The quantitative Neumann inverse used for the actual coefficient perturbation. -/

noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def oneSubInverse (K : E →L[ℝ] E) (hK : ‖K‖ < 1) : E →L[ℝ] E :=
  ↑((Units.oneSub K hK)⁻¹)

theorem oneSubInverse_equation (K : E →L[ℝ] E) (hK : ‖K‖ < 1) (f : E) :
    oneSubInverse K hK f - K (oneSubInverse K hK f) = f := by
  have h : ((Units.oneSub K hK : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) *
      ↑((Units.oneSub K hK)⁻¹) = 1 := (Units.oneSub K hK).val_inv
  have he := congrArg (fun T : E →L[ℝ] E => T f) h
  simpa only [Units.val_oneSub, mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, oneSubInverse] using he

theorem oneSubInverse_bound (K : E →L[ℝ] E) (hK : ‖K‖ < 1) (f : E) :
    ‖oneSubInverse K hK f‖ ≤ ‖f‖ / (1 - ‖K‖) := by
  have he := oneSubInverse_equation K hK f
  have hy : oneSubInverse K hK f = f + K (oneSubInverse K hK f) := by
    exact sub_eq_iff_eq_add.mp he
  have hb : ‖oneSubInverse K hK f‖ ≤ ‖f‖ + ‖K‖ * ‖oneSubInverse K hK f‖ := by
    calc
      _ = ‖f + K (oneSubInverse K hK f)‖ := congrArg norm hy
      _ ≤ ‖f‖ + ‖K (oneSubInverse K hK f)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (K.le_opNorm _)
  apply (le_div_iff₀ (sub_pos.mpr hK)).mpr
  nlinarith

theorem oneSubInverse_unique (K : E →L[ℝ] E) (hK : ‖K‖ < 1) (f u : E)
    (hu : u - K u = f) : u = oneSubInverse K hK f := by
  have hv := oneSubInverse_equation K hK f
  have he : u - oneSubInverse K hK f = K (u - oneSubInverse K hK f) := by
    rw [map_sub]
    calc
      _ = (u - K u) - (oneSubInverse K hK f - K (oneSubInverse K hK f)) +
          (K u - K (oneSubInverse K hK f)) := by abel
      _ = _ := by rw [hu, hv]; abel
  have hb : ‖u - oneSubInverse K hK f‖ ≤ ‖K‖ * ‖u - oneSubInverse K hK f‖ := by
    calc
      _ = ‖K (u - oneSubInverse K hK f)‖ := congrArg norm he
      _ ≤ _ := K.le_opNorm _
  have hz : ‖u - oneSubInverse K hK f‖ = 0 := by
    nlinarith [norm_nonneg (u - oneSubInverse K hK f)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end OAI.Analysis.PDE.Schauder
