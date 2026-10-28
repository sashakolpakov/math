import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleEquatorOrientation
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingLoop
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! # Circle Positive Arcs -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CirclePositiveArcs

noncomputable section

/-!
# ChernClass: an actual positive circle cycle subordinate to the two pole charts

The west and east semicircles run in positive order from the positive
imaginary point. Each lies in the appropriate original pole complement,
so they supply concrete small-chain representatives for its Mayer–Vietoris
normalization.
-/

open _root_.CategoryTheory
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Positive complex exponential in the standard ordered real coordinates. -/
def realCircleExponential (θ : ℝ) : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle :=
  ⟨Complex.orthonormalBasisOneI.repr (Complex.exp ((θ : ℂ) * Complex.I)), by
    rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact Complex.norm_exp_ofReal_mul_I θ⟩

theorem continuous_realCircleExponential : Continuous realCircleExponential := by
  unfold realCircleExponential
  fun_prop

theorem realCircleExponential_re (θ : ℝ) : (realCircleExponential θ).val 0 = Real.cos θ := by
  simp [realCircleExponential, Complex.orthonormalBasisOneI_repr_apply, Complex.exp_re]

theorem realCircleExponential_im (θ : ℝ) : (realCircleExponential θ).val 1 = Real.sin θ := by
  simp [realCircleExponential, Complex.orthonormalBasisOneI_repr_apply, Complex.exp_im]

theorem realCircleExponential_pi_add (θ : ℝ) :
    realCircleExponential (Real.pi + θ) = -realCircleExponential θ := by
  apply Subtype.ext
  change Complex.orthonormalBasisOneI.repr (Complex.exp (((Real.pi + θ : ℝ) : ℂ) * Complex.I)) =
    -Complex.orthonormalBasisOneI.repr (Complex.exp ((θ : ℂ) * Complex.I))
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, neg_one_mul, map_neg]

theorem realCircleExponential_pi_half : realCircleExponential (Real.pi / 2) = CircleEquatorOrientation.positiveCirclePoint := by
  apply Subtype.ext
  ext i
  fin_cases i
  · simp [realCircleExponential_re, CircleEquatorOrientation.positiveCirclePoint]
  · simp [realCircleExponential_im, CircleEquatorOrientation.positiveCirclePoint]

/-- The positive west semicircle, from `i` to `-i`. -/
def positiveWestArcMap : C(Convexity.StdSimplex ℝ (Fin 2), CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) :=
  ⟨fun t => realCircleExponential (Real.pi / 2 + Real.pi * t.weights 1), by
    apply continuous_realCircleExponential.comp
    exact continuous_const.add (continuous_const.mul
      (Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 2)))⟩

/-- The following positive east semicircle, from `-i` to `i`. -/
def positiveEastArcMap : C(Convexity.StdSimplex ℝ (Fin 2), CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) :=
  ⟨fun t => -positiveWestArcMap t, by fun_prop⟩

theorem positiveWestArc_re_nonpos (t : Convexity.StdSimplex ℝ (Fin 2)) :
    (positiveWestArcMap t).val 0 ≤ 0 := by
  change (realCircleExponential (Real.pi / 2 + Real.pi * t.weights 1)).val 0 ≤ 0
  rw [realCircleExponential_re, Real.cos_add]
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, neg_nonpos]
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg Real.pi_pos.le (t.weights_nonneg 1))
    (by
      have ht : t.weights 1 ≤ 1 := Convexity.StdSimplex.weights_apply_le_one t 1
      nlinarith [Real.pi_pos])

theorem positiveWestArc_firstChart (t : Convexity.StdSimplex ℝ (Fin 2)) :
    positiveWestArcMap t ∈ CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart := by
  intro h
  have hr := positiveWestArc_re_nonpos t
  have he := congrArg (fun x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle => x.val 0) h
  have he' : (positiveWestArcMap t).val 0 = 1 := by simpa [CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] using he
  linarith

theorem positiveEastArc_secondChart (t : Convexity.StdSimplex ℝ (Fin 2)) :
    positiveEastArcMap t ∈ CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart := by
  intro h
  have hr := positiveWestArc_re_nonpos t
  have he := congrArg (fun x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle => x.val 0) h
  have he' : -(positiveWestArcMap t).val 0 = -1 := by
    simpa [positiveEastArcMap, CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] using he
  linarith

theorem positiveWestArc_start : positiveWestArcMap (Convexity.StdSimplex.single 0) = CircleEquatorOrientation.positiveCirclePoint := by
  simpa [positiveWestArcMap, Convexity.StdSimplex.single] using realCircleExponential_pi_half

theorem positiveWestArc_end : positiveWestArcMap (Convexity.StdSimplex.single 1) = -CircleEquatorOrientation.positiveCirclePoint := by
  have h : Real.pi / 2 + Real.pi * (Convexity.StdSimplex.single (1 : Fin 2) : Convexity.StdSimplex ℝ (Fin 2)).weights 1 =
      Real.pi + Real.pi / 2 := by simp [add_comm]
  change realCircleExponential _ = _
  rw [h, realCircleExponential_pi_add, realCircleExponential_pi_half]

theorem positiveEastArc_start : positiveEastArcMap (Convexity.StdSimplex.single 0) = -CircleEquatorOrientation.positiveCirclePoint :=
  congrArg Neg.neg positiveWestArc_start

theorem positiveEastArc_end : positiveEastArcMap (Convexity.StdSimplex.single 1) = CircleEquatorOrientation.positiveCirclePoint := by
  change -positiveWestArcMap (Convexity.StdSimplex.single 1) = _
  rw [positiveWestArc_end, neg_neg]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CirclePositiveArcs
