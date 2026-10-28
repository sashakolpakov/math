import OAI.Geometry.Nikodym.Definitions
import OAI.MeasureTheory.Kakeya.Measurability

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OAI.Geometry.Nikodym

theorem lowerSemicontinuous_nikodym_slice {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) (ω : Space n) (t : ℝ) :
    LowerSemicontinuous (fun x =>
      (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω), ‖f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω))) := by
  let F : Space n → Space n → ℝ≥0∞ := fun x y =>
    (OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω)).indicator
      (fun y => ‖f y‖ₑ / volume (OAI.MeasureTheory.Kakeya.tube δ ω 0)) y
  have hm (x : Space n) : AEMeasurable (F x) (volume : Measure (Space n)) :=
    (hf.enorm.div_const _).indicator (OAI.MeasureTheory.Kakeya.measurableSet_tube _ _ _)
  have hl (y : Space n) : LowerSemicontinuous (fun x => F x y) := by
    change LowerSemicontinuous
      ({x : Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω)}.indicator
        (fun _ => ‖f y‖ₑ / volume (OAI.MeasureTheory.Kakeya.tube δ ω 0)))
    have ho : IsOpen {x : Space n | y ∈ OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω)} :=
      (OAI.MeasureTheory.Kakeya.isOpen_tube_parameter_set δ y).preimage
        (show Continuous (fun x : Space n => (ω,x-t • ω)) by fun_prop)
    exact ho.lowerSemicontinuous_indicator bot_le
  have h := OAI.MeasureTheory.Kakeya.lowerSemicontinuous_lintegral_family F hm hl
  convert h using 1
  funext x
  rw [show (∫⁻ y, F x y) = ∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω (x-t • ω),
      ‖f y‖ₑ / volume (OAI.MeasureTheory.Kakeya.tube δ ω 0) from
    lintegral_indicator (OAI.MeasureTheory.Kakeya.measurableSet_tube _ _ _) _]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hf.restrict.enorm,OAI.MeasureTheory.Kakeya.volume_tube_center_eq]

theorem lowerSemicontinuous_nikodymMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    LowerSemicontinuous (nikodymMaximal δ f) := by
  unfold nikodymMaximal
  exact lowerSemicontinuous_iSup fun ω => lowerSemicontinuous_iSup fun _ =>
    lowerSemicontinuous_iSup fun t => lowerSemicontinuous_iSup fun _ =>
      lowerSemicontinuous_nikodym_slice δ f hf ω t

theorem measurable_nikodymMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) :
    Measurable (nikodymMaximal δ f) :=
  (lowerSemicontinuous_nikodymMaximal δ f hf).measurable

end OAI.Geometry.Nikodym
