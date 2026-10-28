import OAI.Analysis.PDE.Nonlinear.AverageHolder

/-! Smallness of the averaged coefficient from small endpoint oscillations. -/

noncomputable section
open Set Metric _root_.MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder

theorem segmentAverage_self {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (g : E → F) (a : E) :
    segmentAverage g a a = g a := by
  have he (t : ℝ) : segmentPoint a a t = a := by
    rw [segmentPoint, ← add_smul]
    simp only [sub_add_cancel, one_smul]
  simp only [segmentAverage, he, intervalIntegral.integral_const, sub_zero, one_smul]

theorem exists_small_segmentAverage {X E F : Type*}
    [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) (hg : Continuous g) {α R L δa δb : ℝ}
    (hα : 0 < α) (hL : 0 ≤ L) (haδ : 0 ≤ δa) (hbδ : 0 ≤ δb)
    (hLip : ∀ x, ‖x‖ ≤ R → ∀ y, ‖y‖ ≤ R → ‖g x - g y‖ ≤ L * ‖x - y‖)
    (a : E) (ha : ‖a‖ ≤ R) (A B : X → E)
    (hA : ∀ x, ‖A x‖ ≤ R) (hB : ∀ x, ‖B x‖ ≤ R)
    (hAa : ∀ x, ‖A x - a‖ ≤ δa) (hBa : ∀ x, ‖B x - a‖ ≤ δb)
    (hAH : ∀ x y, ‖A x - A y‖ ≤ δa * (dist x y) ^ α)
    (hBH : ∀ x y, ‖B x - B y‖ ≤ δb * (dist x y) ^ α) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap X F α,
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = segmentAverage g (A x) (B x) - g a) ∧
      ‖H‖ ≤ L * (δa + δb) := by
  let f : X → F := fun x => segmentAverage g (A x) (B x) - g a
  have hf (x) : ‖f x‖ ≤ L * (δa + δb) := by
    change ‖segmentAverage g (A x) (B x) - g a‖ ≤ _
    rw [← segmentAverage_self g a]
    exact (segmentAverage_sub_le g hg hL hLip (hA x) (hB x) ha ha).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hAa x) (hBa x)) hL)
  have hh (x y) : ‖f x - f y‖ ≤ (L * (δa + δb)) * (dist x y) ^ α := by
    have he : f x - f y = segmentAverage g (A x) (B x) - segmentAverage g (A y) (B y) := by
      dsimp only [f]
      abel
    rw [he]
    calc
      _ ≤ L * (‖A x - A y‖ + ‖B x - B y‖) :=
        segmentAverage_sub_le g hg hL hLip (hA x) (hB x) (hA y) (hB y)
      _ ≤ L * (δa * (dist x y) ^ α + δb * (dist x y) ^ α) :=
        mul_le_mul_of_nonneg_left (add_le_add (hAH x y) (hBH x y)) hL
      _ = _ := by ring
  let fbc : X →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup f
    (continuous_of_holder_bound hα hh) (L * (δa + δb)) hf
  let H : OAI.Analysis.Normed.Function.Holder.HolderMap X F α := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le fbc hh
  refine ⟨H, fun _ => rfl, ?_⟩
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα.le (by positivity)
  · exact hf
  · exact hh

end OAI.Analysis.PDE.Nonlinear
