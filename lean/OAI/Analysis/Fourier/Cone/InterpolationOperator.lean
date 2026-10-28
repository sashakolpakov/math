import OAI.Analysis.Fourier.Restriction.Diagonal

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone

/-- A unit-modulus integral extension operator on a finite source measure.
These are elementary integral properties, not an interpolation assumption. -/
structure FiniteExtension {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) where
  apply : (X → ℂ) → Y → ℂ
  measurable : ∀ f, Integrable f μ → Measurable (apply f)
  map_add : ∀ f g, Integrable f μ → Integrable g μ → ∀ y,
    apply (fun x => f x + g x) y = apply f y + apply g y
  map_const_mul : ∀ (c : ℂ) f y, apply (fun x => c * f x) y = c * apply f y
  congr_ae : ∀ {f g}, f =ᵐ[μ] g → ∀ y, apply f y = apply g y
  bound : ∀ f y, ‖apply f y‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ
  map_zero : ∀ y, apply (fun _ => 0) y = 0

instance {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} : CoeFun (FiniteExtension μ ν)
      (fun _ => (X → ℂ) → Y → ℂ) := ⟨OAI.Analysis.Fourier.Cone.FiniteExtension.apply⟩

namespace FiniteExtension

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} {T : FiniteExtension μ ν}

theorem norm_le_of_normalized_moment {g : X → ℂ} (hg : Measurable g)
    {a : ℝ} (ha : 1 ≤ a) (hgn : (∫⁻ x, ‖g x‖ₑ ^ a ∂μ) ≤ 1) (y : Y) :
    ‖T g y‖ ≤ (μ univ).toReal + 1 := by
  have H := (T.bound g y).trans (OAI.Analysis.Fourier.Restriction.lintegral_enorm_le_measure_add_one μ hg ha hgn)
  have ht : μ univ + 1 ≠ (⊤ : ℝ≥0∞) := by finiteness
  have Hr := ENNReal.toReal_mono ht H
  simpa [ENNReal.toReal_add (measure_ne_top _ _) (by simp : (1 : ℝ≥0∞) ≠ ⊤)] using Hr

end FiniteExtension
end OAI.Analysis.Fourier.Cone
