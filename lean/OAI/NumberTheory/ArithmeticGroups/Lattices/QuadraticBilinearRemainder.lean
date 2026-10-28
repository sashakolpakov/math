import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Quadratic Bilinear Remainder -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QuadraticBilinearRemainder.Construction

noncomputable section

/-! The linearized equation at a zero of a continuous quadratic map
is bounded by the quadratic remainder at every nearby zero. -/

theorem bilinear_quadratic_linearization_eq_neg
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : V →L[ℝ] V →L[ℝ] F) (b x : V) (hb : Q b b = 0) (hx : Q (b + x) (b + x) = 0) :
    Q b x + Q x b = -Q x x := by
  simp only [map_add, add_apply, hb, zero_add] at hx
  apply eq_neg_iff_add_eq_zero.mpr
  convert hx using 1
  abel

theorem bilinear_quadratic_linearization_norm_bound
    {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : V →L[ℝ] V →L[ℝ] F) (b x : V) (hb : Q b b = 0) (hx : Q (b + x) (b + x) = 0) :
    ‖Q b x + Q x b‖ ≤ ‖Q‖ * ‖x‖ ^ 2 := by
  rw [bilinear_quadratic_linearization_eq_neg Q b x hb hx, norm_neg]
  convert ContinuousLinearMap.le_opNorm₂ Q x x using 1
  ring

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QuadraticBilinearRemainder.Construction
