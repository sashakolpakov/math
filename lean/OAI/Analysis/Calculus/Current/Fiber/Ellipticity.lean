import OAI.Analysis.Calculus.Current.Fiber.Rescale

/-! Uniform ellipticity on the true fibers, including the small-time scaling. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion
open scoped Matrix Matrix.Norms.Elementwise

def fiberSpatialForm {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q) : ℝ :=
  (star (fiberSpatialLift v) ⬝ᵥ
    (fiberHessian (1 / 10) a z *ᵥ fiberSpatialLift v)).re

theorem fiberHessian_uniform_spatial_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (z : Index d → ℂ), 0 < a →
      fiberDefining (1 / 10) a z ≤ 0 → a ≤ ‖imaginaryTime z‖ → ‖imaginaryTime z‖ ≤ 4 →
      ∀ v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q, c * ‖v‖ ^ 2 ≤ fiberSpatialForm a z v := by
  obtain ⟨c, hc, hbound⟩ := fiberHessian_uniform_weighted_lower d
  refine ⟨c / 144, by positivity, ?_⟩
  intro a z ha hr ht ht4 v
  have hay := fiber_height_ge_scale a ha z hr ht
  have hy : ‖z none‖ ≤ 12 := (fiber_height_le_time a ha z hr ht).trans (by linarith)
  have hY : z none ≠ 0 := norm_pos_iff.mp (ha.trans_le hay)
  have hn := fiberHessian_nonneg (1 / 10) a z hY (fiberSpatialLift v)
  have hw := hbound a z ha hay hr v
  have hs : ‖z none‖ ^ 2 ≤ 144 := by nlinarith [norm_nonneg (z none)]
  have hm := mul_le_mul_of_nonneg_right hs hn
  change c / 144 * ‖v‖ ^ 2 ≤ _
  dsimp [fiberSpatialForm]
  nlinarith

theorem fiberHessian_small_time_spatial_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (z : Index d → ℂ), 0 < a →
      fiberDefining (1 / 10) a z ≤ 0 → a ≤ ‖imaginaryTime z‖ → ‖imaginaryTime z‖ ≤ 4 * a →
      ∀ v : Option (Fin d) → OAI.Analysis.Calculus.Quaternion.Q, (c / a ^ 2) * ‖v‖ ^ 2 ≤ fiberSpatialForm a z v := by
  obtain ⟨c, hc, hbound⟩ := fiberHessian_uniform_weighted_lower d
  refine ⟨c / 144, by positivity, ?_⟩
  intro a z ha hr ht ht4 v
  have hay := fiber_height_ge_scale a ha z hr ht
  have hy : ‖z none‖ ≤ 12 * a := (fiber_height_le_time a ha z hr ht).trans (by linarith)
  have hY : z none ≠ 0 := norm_pos_iff.mp (ha.trans_le hay)
  have hn := fiberHessian_nonneg (1 / 10) a z hY (fiberSpatialLift v)
  have hw := hbound a z ha hay hr v
  have hs : ‖z none‖ ^ 2 ≤ 144 * a ^ 2 := by nlinarith [norm_nonneg (z none)]
  have hm := mul_le_mul_of_nonneg_right hs hn
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  dsimp [fiberSpatialForm]
  nlinarith

end OAI.Analysis.Calculus.Current
