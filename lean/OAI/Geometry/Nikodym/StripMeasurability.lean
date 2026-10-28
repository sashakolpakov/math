import OAI.Geometry.Nikodym.StripMaximal
import OAI.MeasureTheory.Kakeya.Measurability

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem isOpen_strip_parameter {d : ℕ} (δ : ℝ) (v : Space d) (p : Space d × ℝ) :
    IsOpen {x : Space d | p ∈ neighborhood δ (linePiece x v 1 2)} := by
  have he : {x : Space d | p ∈ neighborhood δ (linePiece x v 1 2)} =
      ⋃ t ∈ Icc (1:ℝ) 2, {x : Space d | dist p (x+t • v,t) < δ} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion,exists_prop,neighborhood,linePiece]
    constructor
    · rintro ⟨q,⟨t,ht,rfl⟩,hp⟩
      exact ⟨t,ht,hp⟩
    · rintro ⟨t,ht,hp⟩
      exact ⟨(x+t • v,t),⟨t,ht,rfl⟩,hp⟩
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_lt (by fun_prop) continuous_const

theorem lowerSemicontinuous_strip_average {d : ℕ} (δ : ℝ) (v : Space d)
    {f : Space (d+1) → ℂ} (hf : Measurable f) :
    LowerSemicontinuous (fun x : Space d =>
      (∫⁻ p in neighborhood δ (linePiece x v 1 2), ‖f (projectiveJoin d p)‖ₑ) /
        ENNReal.ofReal (δ^d)) := by
  let F : Space d → (Space d × ℝ) → ℝ≥0∞ := fun x =>
    (neighborhood δ (linePiece x v 1 2)).indicator
      (fun p => ‖f (projectiveJoin d p)‖ₑ * (ENNReal.ofReal (δ^d))⁻¹)
  have hm (x : Space d) : AEMeasurable (F x) volume :=
    (((hf.comp (projectiveJoin d).continuous.measurable).enorm.mul_const _).indicator
      (isOpen_neighborhood _ _).measurableSet).aemeasurable
  have hl (p : Space d × ℝ) : LowerSemicontinuous (fun x => F x p) := by
    change LowerSemicontinuous ({x : Space d | p ∈ neighborhood δ (linePiece x v 1 2)}.indicator
      (fun _ => ‖f (projectiveJoin d p)‖ₑ * (ENNReal.ofReal (δ^d))⁻¹))
    exact (isOpen_strip_parameter δ v p).lowerSemicontinuous_indicator bot_le
  have hh := OAI.MeasureTheory.Kakeya.lowerSemicontinuous_lintegral_family F hm hl
  convert hh using 1
  funext x
  rw [lintegral_indicator (isOpen_neighborhood _ _).measurableSet]
  have hm0 : Measurable (fun p : Space d × ℝ => ‖f (projectiveJoin d p)‖ₑ) :=
    (hf.comp (projectiveJoin d).continuous.measurable).enorm
  rw [lintegral_mul_const _ hm0]
  rfl

theorem measurable_stripMaximal {d : ℕ} (δ V : ℝ)
    {f : Space (d+1) → ℂ} (hf : Measurable f) : Measurable (stripMaximal δ V f) := by
  apply LowerSemicontinuous.measurable
  exact lowerSemicontinuous_iSup fun v => lowerSemicontinuous_iSup fun _ =>
    lowerSemicontinuous_strip_average δ v hf

end OAI.Geometry.Nikodym
