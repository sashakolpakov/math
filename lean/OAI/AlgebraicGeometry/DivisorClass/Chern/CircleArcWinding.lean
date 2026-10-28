import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.CirclePositiveArcs
import OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
import OAI.AlgebraicTopology.Duality.Poincare.ConnectingRepresentatives

/-! # Circle Arc Winding -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CircleArcWinding

noncomputable section

section

/-! Actual vertex and edge chains for the circle normalization calculation. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def integralPointChain (X : TopCat.{0}) (x : X) : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X 0 :=
  AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) ((TopCat.toSSetObj₀Equiv (X := X)).symm x)

def integralEdgeChain (X : TopCat.{0}) (c : C(Convexity.StdSimplex ℝ (Fin 2), X)) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X 1 :=
  AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) ((X.toSSetObjEquiv _).symm c)

theorem integralPointChain_map {X Y : TopCat.{0}} (f : X ⟶ Y) (x : X) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f).f 0 (integralPointChain X x) = integralPointChain Y (f x) := by
  have h := ConcreteCategory.congr_hom (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X)
    (TopCat.toSSet.obj Y) (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)
    ((TopCat.toSSetObj₀Equiv (X := X)).symm x)) 1
  refine h.trans ?_
  congr 1

/-- The integral boundary convention is end minus start. -/
theorem integralEdgeChain_boundary (X : TopCat.{0}) (c : C(Convexity.StdSimplex ℝ (Fin 2), X)) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).d 1 0 (integralEdgeChain X c) =
      integralPointChain X (c (Convexity.StdSimplex.single 1)) - integralPointChain X (c (Convexity.StdSimplex.single 0)) := by
  let s : (TopCat.toSSet.obj X) _⦋1⦌ := (X.toSSetObjEquiv _).symm c
  have h0 : (TopCat.toSSet.obj X).δ 0 s =
      (TopCat.toSSetObj₀Equiv (X := X)).symm (c (Convexity.StdSimplex.single 1)) := by
    apply (TopCat.toSSetObj₀Equiv (X := X)).injective
    rw [WindingSingular.singularEdge_vertex, Equiv.apply_symm_apply]
    rfl
  have h1 : (TopCat.toSSet.obj X).δ 1 s =
      (TopCat.toSSetObj₀Equiv (X := X)).symm (c (Convexity.StdSimplex.single 0)) := by
    apply (TopCat.toSSetObj₀Equiv (X := X)).injective
    rw [WindingSingular.singularEdge_vertex, Equiv.apply_symm_apply]
    rfl
  refine (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain_boundary (R := ℤ) (TopCat.toSSet.obj X) (n := 0) s).trans ?_
  let v : Fin 2 → (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X 0 := fun i =>
    ((-1 : ℤ) ^ i.val) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) ((TopCat.toSSet.obj X).δ i s)
  refine (Fin.sum_univ_two v).trans ?_
  change ((-1 : ℤ) ^ 0) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) ((TopCat.toSSet.obj X).δ 0 s) +
      ((-1 : ℤ) ^ 1) • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) ((TopCat.toSSet.obj X).δ 1 s) = _
  rw [pow_zero, one_zsmul, pow_one, neg_one_zsmul, h0, h1]
  exact (sub_eq_add_neg _ _).symm

/-- The actual positive west arc regarded as a simplex of its original chart. -/
def positiveWestChartArc : C(Convexity.StdSimplex ℝ (Fin 2), TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleFirstChart) :=
  ⟨fun t => ⟨CirclePositiveArcs.positiveWestArcMap t, CirclePositiveArcs.positiveWestArc_firstChart t⟩,
    CirclePositiveArcs.positiveWestArcMap.continuous.subtype_mk _⟩

def positiveEastChartArc : C(Convexity.StdSimplex ℝ (Fin 2), TopCat.of CycleClass.Geometric.SmallCircleHomology.Cycles.circleSecondChart) :=
  ⟨fun t => ⟨CirclePositiveArcs.positiveEastArcMap t, CirclePositiveArcs.positiveEastArc_secondChart t⟩,
    CirclePositiveArcs.positiveEastArcMap.continuous.subtype_mk _⟩

/-- The negative imaginary endpoint lies in both original charts. -/
def negativeCircleOverlap : CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap :=
  ⟨-CircleEquatorOrientation.positiveCirclePoint, by
    constructor <;> intro h
    · have hc := congrArg (fun x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle => x.val (0 : Fin 2)) h
      simp [CircleEquatorOrientation.positiveCirclePoint, CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at hc
    · have hc := congrArg (fun x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle => x.val (0 : Fin 2)) h
      simp [CircleEquatorOrientation.positiveCirclePoint, CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole] at hc⟩

def circleOverlapDifference : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap).X 0 :=
  integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap negativeCircleOverlap - integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleEquatorOrientation.positiveCircleOverlap

end

/-!
# ChernClass: actual winding of the positively traversed two-chart circle

Continuous logarithms along the two actual semicircles give total increment
two pi i. Endpoint logarithms cancel, independently of their branches.
-/

open _root_.CategoryTheory OAI.AlgebraicTopology.Cohomology.Singular.ChainDual
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def circleComplexCoordinate : C(CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle, ℂ) :=
  ⟨fun x => Complex.orthonormalBasisOneI.repr.symm x.val,
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val⟩

theorem circleComplexCoordinate_ne_zero (x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) : circleComplexCoordinate x ≠ 0 := by
  intro h
  have hn : ‖circleComplexCoordinate x‖ = 1 :=
    (Complex.orthonormalBasisOneI.repr.symm.norm_map _).trans (norm_eq_of_mem_sphere x)
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem circleComplexCoordinate_exponential (θ : ℝ) :
    circleComplexCoordinate (CirclePositiveArcs.realCircleExponential θ) = Complex.exp ((θ : ℂ) * Complex.I) :=
  Complex.orthonormalBasisOneI.repr.symm_apply_apply _

theorem circleComplexCoordinate_neg (x : CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) :
    circleComplexCoordinate (-x) = -circleComplexCoordinate x :=
  map_neg Complex.orthonormalBasisOneI.repr.symm x.val

def positiveWestArcLog : C(Convexity.StdSimplex ℝ (Fin 2), ℂ) :=
  ⟨fun t => ((Real.pi : ℂ) / 2 + (Real.pi : ℂ) * (t.weights 1 : ℂ)) * Complex.I, by
    exact (continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp (Convexity.StdSimplex.continuous_weights_apply ℝ (1 : Fin 2))))).mul continuous_const⟩

def positiveEastArcLog : C(Convexity.StdSimplex ℝ (Fin 2), ℂ) :=
  positiveWestArcLog + ContinuousMap.const _ ((Real.pi : ℂ) * Complex.I)

def positiveWestCircleSimplex : (TopCat.toSSet.obj CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) _⦋1⦌ :=
  (CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle.toSSetObjEquiv _).symm CirclePositiveArcs.positiveWestArcMap

def positiveEastCircleSimplex : (TopCat.toSSet.obj CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle) _⦋1⦌ :=
  (CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle.toSSetObjEquiv _).symm CirclePositiveArcs.positiveEastArcMap

theorem positiveWestArcLog_exp (t : Convexity.StdSimplex ℝ (Fin 2)) :
    Complex.exp (positiveWestArcLog t) =
      WindingSingular.simplexFunction CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle circleComplexCoordinate positiveWestCircleSimplex t := by
  change Complex.exp (positiveWestArcLog t) = circleComplexCoordinate (CirclePositiveArcs.positiveWestArcMap t)
  rw [show CirclePositiveArcs.positiveWestArcMap t = CirclePositiveArcs.realCircleExponential (Real.pi / 2 + Real.pi * t.weights 1) from rfl,
    circleComplexCoordinate_exponential]
  simp only [positiveWestArcLog, ContinuousMap.coe_mk, Complex.ofReal_add,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_mul]

theorem positiveEastArcLog_exp (t : Convexity.StdSimplex ℝ (Fin 2)) :
    Complex.exp (positiveEastArcLog t) =
      WindingSingular.simplexFunction CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle circleComplexCoordinate positiveEastCircleSimplex t := by
  change Complex.exp (positiveWestArcLog t + (Real.pi : ℂ) * Complex.I) =
    circleComplexCoordinate (-CirclePositiveArcs.positiveWestArcMap t)
  rw [Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one, circleComplexCoordinate_neg]
  exact congrArg Neg.neg (positiveWestArcLog_exp t)

/-- The two actual integral edges have total positive winding one. -/
theorem positiveCircleArcs_winding :
    WindingSingular.singularWindingValue CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle circleComplexCoordinate circleComplexCoordinate_ne_zero positiveWestCircleSimplex +
      WindingSingular.singularWindingValue CycleClass.Geometric.SmallCircleHomology.Cycles.standardCircle circleComplexCoordinate circleComplexCoordinate_ne_zero positiveEastCircleSimplex = 1 := by
  apply Rat.cast_injective (α := ℂ)
  apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
  rw [Rat.cast_add, add_mul, WindingSingular.singularWindingValue_period, WindingSingular.singularWindingValue_period,
    WindingSingular.singularLogIncrement_of_log _ _ _ _ positiveWestArcLog positiveWestArcLog_exp,
    WindingSingular.singularLogIncrement_of_log _ _ _ _ positiveEastArcLog positiveEastArcLog_exp]
  change positiveWestArcLog (Convexity.StdSimplex.single 1) - positiveWestArcLog (Convexity.StdSimplex.single 0) +
      Complex.log (circleComplexCoordinate (CirclePositiveArcs.positiveWestArcMap (Convexity.StdSimplex.single 0))) -
      Complex.log (circleComplexCoordinate (CirclePositiveArcs.positiveWestArcMap (Convexity.StdSimplex.single 1))) +
    (positiveEastArcLog (Convexity.StdSimplex.single 1) - positiveEastArcLog (Convexity.StdSimplex.single 0) +
      Complex.log (circleComplexCoordinate (CirclePositiveArcs.positiveEastArcMap (Convexity.StdSimplex.single 0))) -
      Complex.log (circleComplexCoordinate (CirclePositiveArcs.positiveEastArcMap (Convexity.StdSimplex.single 1)))) = _
  rw [CirclePositiveArcs.positiveWestArc_start, CirclePositiveArcs.positiveWestArc_end, CirclePositiveArcs.positiveEastArc_start, CirclePositiveArcs.positiveEastArc_end]
  simp only [positiveWestArcLog, positiveEastArcLog, ContinuousMap.coe_mk,
    ContinuousMap.add_apply, ContinuousMap.const_apply, Convexity.StdSimplex.single,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, add_zero, Rat.cast_one, one_mul]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CircleArcWinding
