import OAI.Analysis.Fourier.Cone.InterpolationPower

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone.FiniteExtension

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} {T : FiniteExtension μ ν}

def mixedExtensionConstant (μ : Measure X) (a s b : ℝ) (C : ℝ≥0∞) : ℝ≥0∞ :=
  2 * (C ^ s * ENNReal.ofReal
    (b * (((μ univ).toReal + 1) ^ (b - a * (s - 1) / (a - 1)) /
      (b - a * (s - 1) / (a - 1))))) ^ (1 / b)

omit [IsFiniteMeasure μ] in
theorem mixedExtensionConstant_ne_top {a s b : ℝ} {C : ℝ≥0∞}
    (hs : 0 ≤ s) (hb : 0 < b) (hC : C ≠ ⊤) :
    FiniteExtension.mixedExtensionConstant μ a s b C ≠ ⊤ := by
  unfold FiniteExtension.mixedExtensionConstant
  apply ENNReal.mul_ne_top (by norm_num)
  apply ne_of_lt
  apply ENNReal.rpow_lt_top_of_nonneg (le_of_lt (one_div_pos.mpr hb))
  exact ENNReal.mul_ne_top (ne_of_lt (ENNReal.rpow_lt_top_of_nonneg hs hC))
    ENNReal.ofReal_ne_top

/-- Every diagonal extension bound gives the strict mixed bounds above its
interpolation line, initially for normalized measurable inputs. -/
theorem mixed_normalized {a s b : ℝ}
    (ha : 1 < a) (has : a ≤ s) (hb : 0 < b)
    (hab : a * (s - 1) / (a - 1) < b) {C : ℝ≥0∞}
    (hdiag : ∀ g : X → ℂ, MemLp g (ENNReal.ofReal s) μ →
      eLpNorm (T g) (ENNReal.ofReal s) ν ≤
        C * eLpNorm g (ENNReal.ofReal s) μ)
    {g : X → ℂ} (hgm : Measurable g) (hgi : Integrable g μ)
    (hgn : (∫⁻ ω, ‖g ω‖ₑ ^ a ∂μ) ≤ 1) :
    eLpNorm (T g) (ENNReal.ofReal b) ν ≤
      FiniteExtension.mixedExtensionConstant μ a s b C := by
  have hEm := (T.measurable g hgi)
  have H := OAI.Analysis.Fourier.Restriction.lintegral_power_le_of_weak_and_bounded ν
    (hEm.norm.div_const 2) (fun x ↦ div_nonneg (norm_nonneg _) (by norm_num))
    (show 0 ≤ (μ univ).toReal + 1 by positivity)
    (fun x ↦ by
      have hx := FiniteExtension.norm_le_of_normalized_moment (T := T) hgm ha.le hgn x
      have hn := norm_nonneg (T g x)
      linarith) hb hab (A := C ^ s) (fun t ht ↦ by
      have he : {x | t < ‖T g x‖ / 2} =
          {x | 2 * t < ‖T g x‖} := by
        ext x
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro hx <;> linarith
      rw [he]
      exact FiniteExtension.weak_mixed ha has hdiag hgm hgi hgn ht)
  exact OAI.Analysis.Fourier.Restriction.eLpNorm_le_of_half_moment_bound ν hEm hb H

end OAI.Analysis.Fourier.Cone.FiniteExtension
