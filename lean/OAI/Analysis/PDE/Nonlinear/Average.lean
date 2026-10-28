import OAI.Analysis.Normed.Function.Holder.Banach.Composition
import OAI.Analysis.PDE.Dirichlet.HolderCompactness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Quantitative endpoint bounds for the actual segment average of a smooth coefficient. -/

noncomputable section
open Set Metric _root_.MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder

def segmentPoint {E : Type*} [AddCommGroup E] [Module ℝ E] (a b : E) (t : ℝ) : E :=
  (1 - t) • a + t • b

def segmentAverage {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F) (a b : E) : F :=
  ∫ t in (0 : ℝ)..1, g (segmentPoint a b t)

theorem segmentPoint_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E} {t R : ℝ} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖segmentPoint a b t‖ ≤ R := by
  have h₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  calc
    _ ≤ ‖(1 - t) • a‖ + ‖t • b‖ := norm_add_le _ _
    _ = (1 - t) * ‖a‖ + t * ‖b‖ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg h₁, abs_of_nonneg ht.1]
    _ ≤ (1 - t) * R + t * R := add_le_add (mul_le_mul_of_nonneg_left ha h₁) (mul_le_mul_of_nonneg_left hb ht.1)
    _ = R := by ring

theorem segmentPoint_sub_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c d : E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖segmentPoint a b t - segmentPoint c d t‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  have he : segmentPoint a b t - segmentPoint c d t = (1 - t) • (a - c) + t • (b - d) := by
    simp only [segmentPoint, smul_sub]
    abel
  have h₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  rw [he]
  calc
    _ ≤ ‖(1 - t) • (a - c)‖ + ‖t • (b - d)‖ := norm_add_le _ _
    _ = (1 - t) * ‖a - c‖ + t * ‖b - d‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg h₁, abs_of_nonneg ht.1]
    _ ≤ 1 * ‖a - c‖ + 1 * ‖b - d‖ := add_le_add
      (mul_le_mul_of_nonneg_right (by linarith only [ht.1]) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _))
    _ = _ := by ring

theorem continuous_segmentPoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : E) : Continuous (segmentPoint a b) :=
  ((continuous_const.sub continuous_id).smul continuous_const).add (continuous_id.smul continuous_const)

theorem segmentAverage_norm_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) {R M : ℝ} (hg : ∀ x, ‖x‖ ≤ R → ‖g x‖ ≤ M)
    {a b : E} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) : ‖segmentAverage g a b‖ ≤ M := by
  have hi : ∀ t ∈ uIoc (0 : ℝ) 1, ‖g (segmentPoint a b t)‖ ≤ M := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact hg _ (segmentPoint_norm_le ha hb ht')
  simpa only [segmentAverage, sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hi

theorem segmentAverage_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (hg : Continuous g) {R L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x, ‖x‖ ≤ R → ∀ y, ‖y‖ ≤ R → ‖g x - g y‖ ≤ L * ‖x - y‖)
    {a b c d : E} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) (hd : ‖d‖ ≤ R) :
    ‖segmentAverage g a b - segmentAverage g c d‖ ≤ L * (‖a - c‖ + ‖b - d‖) := by
  unfold segmentAverage
  have hab : IntervalIntegrable (fun t => g (segmentPoint a b t)) volume 0 1 :=
    (hg.comp (continuous_segmentPoint a b)).intervalIntegrable 0 1
  have hcd : IntervalIntegrable (fun t => g (segmentPoint c d t)) volume 0 1 :=
    (hg.comp (continuous_segmentPoint c d)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hab hcd]
  have hi : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖g (segmentPoint a b t) - g (segmentPoint c d t)‖ ≤ L * (‖a - c‖ + ‖b - d‖) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simp only [uIoc_of_le zero_le_one, mem_Ioc] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact (hLip _ (segmentPoint_norm_le ha hb ht') _ (segmentPoint_norm_le hc hd ht')).trans
      (mul_le_mul_of_nonneg_left (segmentPoint_sub_bound a b c d ht') hL)
  simpa only [sub_zero, abs_one, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hi

theorem continuous_of_holder_bound {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    {f : X → F} {α C : ℝ} (hα : 0 < α)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * (dist x y) ^ α) : Continuous f := by
  have he := OAI.Analysis.PDE.Dirichlet.equicontinuous_of_uniform_holder (u := fun _ : Unit => f) hα (fun _ => hf)
  exact he.continuous ()

end OAI.Analysis.PDE.Nonlinear
