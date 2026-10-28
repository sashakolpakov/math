import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem lintegral_translation_average_map {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {S : Set X} {L : X → E} (hL : Measurable L)
    {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ c, ∫⁻ y in S, F (c+L y) ∂ν ∂μ) = ν S * ∫⁻ x, F x ∂μ := by
  rw [lintegral_lintegral_swap]
  · simp only [lintegral_add_right_eq_self,lintegral_const,Measure.restrict_apply_univ]
    exact mul_comm _ _
  · exact (hF.comp (measurable_fst.add (hL.comp measurable_snd))).aemeasurable

theorem lintegral_translation_average {S : Set E} {F : E → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ c, ∫⁻ y in S, F (c+y) ∂μ ∂μ) = μ S * ∫⁻ x, F x ∂μ := by
  rw [lintegral_lintegral_swap]
  · simp only [lintegral_add_right_eq_self,lintegral_const,Measure.restrict_apply_univ]
    exact mul_comm _ _
  · exact (hF.comp (measurable_fst.add measurable_snd)).aemeasurable

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem setLIntegral_translate_closedBall (c : E) (R : ℝ) {F : E → ℝ≥0∞}
    (_ : Measurable F) :
    (∫⁻ y in closedBall 0 R, F (c+y) ∂μ) = ∫⁻ x in closedBall c R, F x ∂μ := by
  have h := lintegral_add_left_eq_self
    ((closedBall c R).indicator F) c (μ:=μ)
  rw [lintegral_indicator isClosed_closedBall.measurableSet] at h
  have he : (fun y => (closedBall c R).indicator F (c+y)) =
      (closedBall 0 R).indicator (fun y => F (c+y)) := by
    funext y
    by_cases hy : y ∈ closedBall 0 R
    · have hcy : c+y ∈ closedBall c R := by simpa [mem_closedBall,dist_eq_norm] using hy
      simp only [indicator_of_mem hy,indicator_of_mem hcy]
    · have hcy : c+y ∉ closedBall c R := by simpa [mem_closedBall,dist_eq_norm] using hy
      simp only [indicator_of_notMem hy,indicator_of_notMem hcy]
  rw [he,lintegral_indicator isClosed_closedBall.measurableSet] at h
  exact h

theorem lintegral_closedBall_average (R : ℝ) {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ c, ∫⁻ x in closedBall c R, F x ∂μ ∂μ) =
      μ (closedBall (0:E) R) * ∫⁻ x, F x ∂μ := by
  simp_rw [← setLIntegral_translate_closedBall μ _ _ hF]
  exact lintegral_translation_average μ hF

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem setLIntegral_translate_ball (c : E) (R : ℝ) {F : E → ℝ≥0∞} :
    (∫⁻ y in ball 0 R, F (c+y) ∂μ) = ∫⁻ x in ball c R, F x ∂μ := by
  have h := lintegral_add_left_eq_self ((ball c R).indicator F) c (μ:=μ)
  rw [lintegral_indicator isOpen_ball.measurableSet] at h
  have he : (fun y => (ball c R).indicator F (c+y)) =
      (ball 0 R).indicator (fun y => F (c+y)) := by
    funext y
    by_cases hy : y ∈ ball 0 R
    · have hcy : c+y ∈ ball c R := by simpa [mem_ball,dist_eq_norm] using hy
      simp only [indicator_of_mem hy,indicator_of_mem hcy]
    · have hcy : c+y ∉ ball c R := by simpa [mem_ball,dist_eq_norm] using hy
      simp only [indicator_of_notMem hy,indicator_of_notMem hcy]
  rw [he,lintegral_indicator isOpen_ball.measurableSet] at h
  exact h

theorem lintegral_ball_average (R : ℝ) {F : E → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ c, ∫⁻ x in ball c R, F x ∂μ ∂μ) = μ (ball (0:E) R) * ∫⁻ x, F x ∂μ := by
  calc
    _ = ∫⁻ c, ∫⁻ y in ball (0:E) R, F (c+y) ∂μ ∂μ := by
      apply lintegral_congr
      intro c
      exact (setLIntegral_translate_ball μ c R).symm
    _ = _ := lintegral_translation_average μ hF

theorem global_bound_of_local_average {F G : E → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) {r R : ℝ} {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hlocal : ∀ c, (∫⁻ x in closedBall c r, F x ∂μ) ≤
      A * ∫⁻ x in closedBall c R, G x ∂μ) :
    μ (closedBall (0:E) r) * ∫⁻ x, F x ∂μ ≤
      A * (μ (closedBall (0:E) R) * ∫⁻ x, G x ∂μ) := by
  rw [← lintegral_closedBall_average μ _ hF,← lintegral_closedBall_average μ _ hG]
  calc
    _ ≤ ∫⁻ c, A * ∫⁻ x in closedBall c R, G x ∂μ ∂μ := lintegral_mono hlocal
    _ = _ := lintegral_const_mul' _ _ hA

end OAI.Geometry.Nikodym
