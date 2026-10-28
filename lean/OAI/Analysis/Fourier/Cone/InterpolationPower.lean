import OAI.Analysis.Fourier.Cone.InterpolationWeak

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone.FiniteExtension

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} {T : FiniteExtension μ ν}

theorem weak_mixed {a s : ℝ}
    (ha : 1 < a) (has : a ≤ s) {C : ℝ≥0∞}
    (hdiag : ∀ g : X → ℂ, MemLp g (ENNReal.ofReal s) μ →
      eLpNorm (T g) (ENNReal.ofReal s) ν ≤
        C * eLpNorm g (ENNReal.ofReal s) μ)
    {g : X → ℂ} (hgm : Measurable g) (hgi : Integrable g μ)
    (hgn : (∫⁻ ω, ‖g ω‖ₑ ^ a ∂μ) ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    ν {x | 2 * t < ‖T g x‖} ≤
      C ^ s * ENNReal.ofReal (t ^ (-(a * (s - 1) / (a - 1)))) := by
  calc
    _ = ν {x | 2 * OAI.Analysis.Fourier.Restriction.mixedThreshold a t ^ (1 - a) < ‖T g x‖} := by
      rw [OAI.Analysis.Fourier.Restriction.mixedThreshold_power ha ht]
    _ ≤ (C ^ s * ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.mixedThreshold a t ^ (s - a))) /
        ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.mixedThreshold a t ^ (1 - a)) ^ s :=
      FiniteExtension.weak_mixed_parameter ha has hdiag hgm hgi hgn
        (OAI.Analysis.Fourier.Restriction.mixedThreshold_pos ht)
    _ = C ^ s * (ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.mixedThreshold a t ^ (s - a)) /
        ENNReal.ofReal (OAI.Analysis.Fourier.Restriction.mixedThreshold a t ^ (1 - a)) ^ s) := by
      simp only [div_eq_mul_inv, mul_assoc]
    _ = _ := by rw [OAI.Analysis.Fourier.Restriction.mixedThreshold_ratio ha (by linarith : 0 ≤ s) ht]

end OAI.Analysis.Fourier.Cone.FiniteExtension
