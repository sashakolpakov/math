import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Hilbert Mean Square Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertMeanSquareBound

noncomputable section

/-! An actual finite-measure mean is bounded by the original integral of the squared norm, from nonnegativity of its variance. -/

open _root_.MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem hilbert_mean_square_bound {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → H) (a : H)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hmean : (∫ x, f x ∂μ) = μ.real Set.univ • a) :
    μ.real Set.univ * ‖a‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hi : Integrable (fun x => inner ℝ a (f x)) μ := hf.const_inner a
  have hc : Integrable (fun _ : X => ‖a‖ ^ 2) μ := integrable_const _
  have hinner : (∫ x, inner ℝ a (f x) ∂μ) = μ.real Set.univ * ‖a‖ ^ 2 := by
    rw [integral_inner hf a, hmean, inner_smul_right, real_inner_self_eq_norm_sq]
  have hv : 0 ≤ ∫ x, (‖a‖ ^ 2 - 2 * inner ℝ a (f x)) + ‖f x‖ ^ 2 ∂μ := by
    apply integral_nonneg
    intro x
    change 0 ≤ ‖a‖ ^ 2 - 2 * inner ℝ a (f x) + ‖f x‖ ^ 2
    rw [← norm_sub_sq_real]
    exact sq_nonneg ‖a - f x‖
  rw [integral_add (f := fun x => ‖a‖ ^ 2 - 2 * inner ℝ a (f x)) (g := fun x => ‖f x‖ ^ 2)
      (hc.sub (hi.const_mul 2)) hf2,
    integral_sub (f := fun _ : X => ‖a‖ ^ 2) (g := fun x => 2 * inner ℝ a (f x)) hc (hi.const_mul 2),
    integral_const_mul, integral_const, hinner, smul_eq_mul] at hv
  linarith only [hv]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HilbertMeanSquareBound
