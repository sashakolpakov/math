import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingSingular

/-! # Winding Loop -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.WindingLoop

noncomputable section

/-!
# ChernClass: positive unit-loop evaluation of actual singular winding

The singular edge parametrized by exp(2πit) has equal endpoints and winding
one. Thus the actual singular winding class on the punctured plane is nonzero.
This uses the constructed simplex logarithm, not a supplied homology generator.
-/

open _root_.CategoryTheory
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

abbrev puncturedPlane : TopCat.{0} := TopCat.of {z : ℂ // z ≠ 0}

def puncturedCoordinate : C(puncturedPlane, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

theorem puncturedCoordinate_ne_zero (z : puncturedPlane) : puncturedCoordinate z ≠ 0 := z.property

/-- The positive logarithm along the actual geometric one-simplex. -/
def positiveLoopLog : C(Convexity.StdSimplex ℝ (Fin 2), ℂ) :=
  ⟨fun t => (2 * (Real.pi : ℂ) * Complex.I) * (t.weights 1 : ℂ),
    continuous_const.mul (Complex.continuous_ofReal.comp
      (Convexity.StdSimplex.continuous_weights_apply ℝ 1))⟩

theorem positiveLoopLog_start : positiveLoopLog (Convexity.StdSimplex.single 0) = 0 := by
  simp [positiveLoopLog, Convexity.StdSimplex.single]

theorem positiveLoopLog_end :
    positiveLoopLog (Convexity.StdSimplex.single 1) = 2 * (Real.pi : ℂ) * Complex.I := by
  simp [positiveLoopLog, Convexity.StdSimplex.single]

/-- The actual positive unit-circle edge, expressed in barycentric coordinates. -/
def positiveLoopMap : C(Convexity.StdSimplex ℝ (Fin 2), puncturedPlane) :=
  ⟨fun t => ⟨Complex.exp (positiveLoopLog t), Complex.exp_ne_zero _⟩, by fun_prop⟩

def positiveLoopSimplex : (TopCat.toSSet.obj puncturedPlane) _⦋1⦌ :=
  (puncturedPlane.toSSetObjEquiv _).symm positiveLoopMap

theorem positiveLoop_vertex_start :
    (puncturedPlane.toSSetObjEquiv _ positiveLoopSimplex (Convexity.StdSimplex.single 0) : ℂ) = 1 := by
  rw [positiveLoopSimplex, Equiv.apply_symm_apply]
  change Complex.exp (positiveLoopLog (Convexity.StdSimplex.single 0)) = 1
  rw [positiveLoopLog_start, Complex.exp_zero]

theorem positiveLoop_vertex_end :
    (puncturedPlane.toSSetObjEquiv _ positiveLoopSimplex (Convexity.StdSimplex.single 1) : ℂ) = 1 := by
  rw [positiveLoopSimplex, Equiv.apply_symm_apply]
  change Complex.exp (positiveLoopLog (Convexity.StdSimplex.single 1)) = 1
  rw [positiveLoopLog_end, Complex.exp_two_pi_mul_I]

/-- Its two singular faces coincide, so it is an actual closed singular path. -/
theorem positiveLoop_faces_equal :
    (TopCat.toSSet.obj puncturedPlane).δ 0 positiveLoopSimplex =
      (TopCat.toSSet.obj puncturedPlane).δ 1 positiveLoopSimplex := by
  apply TopCat.toSSetObj₀Equiv.injective
  rw [WindingSingular.singularEdge_vertex, WindingSingular.singularEdge_vertex]
  apply Subtype.ext
  exact positiveLoop_vertex_end.trans positiveLoop_vertex_start.symm

/-- The constructed winding cocycle evaluates to one on the positive loop. -/
theorem singularWindingValue_positiveLoop :
    WindingSingular.singularWindingValue puncturedPlane puncturedCoordinate puncturedCoordinate_ne_zero positiveLoopSimplex = 1 := by
  apply (Rat.cast_injective (α := ℂ))
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  rw [WindingSingular.singularWindingValue_period]
  have hl : ∀ x, Complex.exp (positiveLoopLog x) =
      WindingSingular.simplexFunction puncturedPlane puncturedCoordinate positiveLoopSimplex x := by
    intro x
    change _ = puncturedCoordinate (puncturedPlane.toSSetObjEquiv _ positiveLoopSimplex x)
    rw [positiveLoopSimplex, Equiv.apply_symm_apply]
    rfl
  rw [WindingSingular.singularLogIncrement_of_log _ _ _ _ positiveLoopLog hl, positiveLoopLog_end, positiveLoopLog_start]
  change (2 * (Real.pi : ℂ) * Complex.I) - 0 +
    Complex.log (puncturedPlane.toSSetObjEquiv _ positiveLoopSimplex (Convexity.StdSimplex.single 0)) -
    Complex.log (puncturedPlane.toSSetObjEquiv _ positiveLoopSimplex (Convexity.StdSimplex.single 1)) = _
  rw [positiveLoop_vertex_start, positiveLoop_vertex_end, Complex.log_one]
  simp

/-- Nonzero winding is proved by evaluation on the actual closed unit loop. -/
theorem singularWindingClass_punctured_ne_zero :
    WindingSingular.singularWindingClass puncturedPlane puncturedCoordinate puncturedCoordinate_ne_zero ≠ 0 := by
  intro hz
  have hclass : AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) puncturedPlane 1
      (WindingSingular.singularWindingCocycle puncturedPlane puncturedCoordinate puncturedCoordinate_ne_zero) =
    AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) puncturedPlane 1 0 := by
    simpa only [WindingSingular.singularWindingClass, map_zero] using hz
  obtain ⟨c, hc⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_eq_iff_exists_succ (ModuleCat.of ℚ ℚ) puncturedPlane 0 _ _).mp hclass
  change (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) puncturedPlane).d 0 1 c =
    WindingSingular.singularWindingCochain puncturedPlane puncturedCoordinate puncturedCoordinate_ne_zero - 0 at hc
  rw [sub_zero] at hc
  have hv := AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_apply (ModuleCat.of ℚ ℚ) puncturedPlane c positiveLoopSimplex
  rw [hc, WindingSingular.singularWindingCochain_value, singularWindingValue_positiveLoop, positiveLoop_faces_equal,
    sub_self] at hv
  exact one_ne_zero hv

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.WindingLoop
