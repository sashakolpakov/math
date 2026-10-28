import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSmallComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleOrientationCoefficient

/-! # Orthant Circle Normalization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantCircleNormalization

noncomputable section

section

/-! The explicit orthant circle has the already proved positive-circle normalization. -/

open _root_.CategoryTheory
open scoped Simplicial

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem orthantEquatorOverlapSimplex_zero (η : Fin 1 → Bool) :
    OrthantBoundaryRepresentatives.orthantEquatorOverlapSimplex 0 η =
      (TopCat.toSSetObj₀Equiv (X := CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap)).symm
        (if η 0 then CircleEquatorOrientation.positiveCircleOverlap else CircleArcWinding.negativeCircleOverlap) := by
  apply (CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap.toSSetObjEquiv _).injective
  apply ContinuousMap.ext
  intro t
  have hv : OrthantSphereEquator.orthantVector 0 η t = EuclideanSpace.single (0 : Fin 1) (OrthantSphereEquator.orthantSign (η 0) : ℝ) := by
    ext i
    have hi : i = 0 := by omega
    subst i
    change (OrthantSphereEquator.orthantSign (η 0) : ℝ) * t.weights 0 = _
    have ht : t.weights 0 = 1 := by
      have h := Convexity.StdSimplex.total_of_fintype t
      change (∑ j : Fin 1, t.weights j) = 1 at h
      simpa only [Fin.sum_univ_one] using h
    rw [ht, mul_one]
    simp
  have hn : ‖OrthantSphereEquator.orthantVector 0 η t‖ = 1 := by
    rw [hv, PiLp.norm_single, OrthantSphereEquator.orthantSign_norm]
  change OrthantSphereEquator.orderedEquatorOverlap 0 (OrthantSphereEquator.orthantSphereMap 0 η t) =
    (if η 0 then CircleEquatorOrientation.positiveCircleOverlap else CircleArcWinding.negativeCircleOverlap)
  apply Subtype.ext
  apply Subtype.ext
  change ((CycleClass.Geometric.SphereCover.Cycles.orderedEquatorCoordinates 1).symm (OrthantSphereEquator.orthantSphereMap 0 η t).val).val = _
  rw [OrthantSphereEquator.orthantSphereMap_coe, hn, inv_one, one_smul, hv]
  change (WithLp.toLp 2 (Fin.cons (α := fun _ : Fin 2 => ℝ) 0
    (fun i : Fin 1 => (EuclideanSpace.single (0 : Fin 1) (OrthantSphereEquator.orthantSign (η 0) : ℝ)) i)) :
      EuclideanSpace ℝ (Fin 2)) = _
  ext i
  fin_cases i <;> cases hb : η 0 <;>
    simp [OrthantSphereEquator.orthantSign, CircleEquatorOrientation.positiveCircleOverlap, CircleArcWinding.negativeCircleOverlap, CircleEquatorOrientation.positiveCirclePoint]

theorem orthantEquatorChain_zero :
    OrthantBoundaryRepresentatives.orthantEquatorChain 0 = CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleEquatorOrientation.positiveCircleOverlap -
      CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleArcWinding.negativeCircleOverlap := by
  rw [OrthantBoundaryRepresentatives.orthantEquatorChain, OrthantBoundaryRepresentatives.sum_orthant_head_tail]
  simp only [Fintype.sum_unique, orthantEquatorOverlapSimplex_zero, Fin.cons_zero,
    Bool.false_eq_true, ite_false, ite_true]
  have hw (b : Bool) : OrthantSphereEquator.orthantWeight (Fin.cons b (default : Fin 0 → Bool)) = OrthantSphereEquator.orthantSign b := by
    rw [OrthantSphereEquator.orthantWeight_cons]
    simp [OrthantSphereEquator.orthantWeight]
  change OrthantSphereEquator.orthantWeight (Fin.cons false (default : Fin 0 → Bool)) • CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleArcWinding.negativeCircleOverlap +
    OrthantSphereEquator.orthantWeight (Fin.cons true (default : Fin 0 → Bool)) • CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleEquatorOrientation.positiveCircleOverlap = _
  rw [hw, hw]
  change (-1 : ℤ) • CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleArcWinding.negativeCircleOverlap +
    (1 : ℤ) • CircleArcWinding.integralPointChain CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap CircleEquatorOrientation.positiveCircleOverlap = _
  rw [neg_one_zsmul, one_zsmul, add_comm, sub_eq_add_neg]

theorem orientedOrthantSmallClass_zero_eq_positiveCircle :
    OrthantSmallCycle.orientedOrthantSmallClass 0 = SmallCirclePositiveCycle.positiveCircleSmallClass := by
  apply CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleBoundary_zero_injective
  rw [OrthantSmallCycle.orientedOrthantSmallClass_boundary, SmallCirclePositiveCycle.positiveCircleSmallClass_boundary]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains CycleClass.Geometric.SmallCircleHomology.Cycles.circleOverlap) 0)
  apply Subtype.ext
  change -(OrthantSmallCycle.orthantEquatorCycle 0).val = CircleArcWinding.circleOverlapDifference
  rw [OrthantSmallCycle.orthantEquatorCycle_val, orthantEquatorChain_zero, neg_sub]
  rfl

theorem orientedOrthantCircle_coordinate :
    CycleClass.Geometric.SphereHomologyInduction.Cycles.standardCircleH1Iso.hom (OrthantSphereCycle.orientedOrthantSphereClass 1) = 1 := by
  rw [← OrthantSmallComparison.orientedOrthantSmallClass_comparison 0]
  change CycleClass.Geometric.SmallCircleHomology.Cycles.smallCircleH1Iso.hom
    ((CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) 1).inv
      ((CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole 1) 1).hom (OrthantSmallCycle.orientedOrthantSmallClass 0))) = 1
  rw [Iso.hom_inv_id_apply, orientedOrthantSmallClass_zero_eq_positiveCircle]
  exact_mod_cast CircleOrientationCoefficient.positiveCircleSmallClass_coordinate.trans CircleEquatorOrientation.chosenCircleEquatorSign_eq_one

end

/-!
# ChernClass: exact normalization of the actual oriented coordinate spheres

The native Mayer–Vietoris map sends each explicit oriented sphere to the
negative of its ordered equator. The circle has coordinate positive one.
Therefore the coordinate of the explicit sphere in dimension d+1 is (-1)^d;
in every odd sphere dimension used by complex local homology it is one.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem orientedOrthantSphereClass_shift (d : ℕ) :
    (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereHomologyShift (d + 1) d).hom (OrthantSphereCycle.orientedOrthantSphereClass (d + 2)) =
      -(OrthantSphereCycle.orientedOrthantSphereClass (d + 1)) := by
  rw [← OrthantSmallComparison.orientedOrthantSmallClass_comparison (d + 1)]
  change (CycleClass.Geometric.SmallSphereHomology.Cycles.standardSphereSmallHomologyShift (d + 2) d).hom
    ((CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (d + 2)) (d + 2)).inv
      ((CycleClass.Geometric.SphereHomologyInduction.Cycles.spherePoleHomologyComparison (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (d + 2)) (d + 2)).hom
        (OrthantSmallCycle.orientedOrthantSmallClass (d + 1)))) = _
  rw [Iso.hom_inv_id_apply, CycleClass.Geometric.SmallSphereHomology.Cycles.standardSphereSmallHomologyShift_hom]
  exact OrthantSmallComparison.orientedOrthantSmallClass_lowerSphere (d + 1)

theorem orientedOrthantSphereClass_coordinate (d : ℕ) :
    (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereTopHomologyIso d).hom (OrthantSphereCycle.orientedOrthantSphereClass (d + 1)) = (-1 : ℤ) ^ d := by
  induction d with
  | zero => exact orientedOrthantCircle_coordinate
  | succ d ih =>
    rw [CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereTopHomologyIso_succ]
    change (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereTopHomologyIso d).hom
      ((CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereHomologyShift (d + 1) d).hom (OrthantSphereCycle.orientedOrthantSphereClass (d + 2))) = _
    rw [orientedOrthantSphereClass_shift, map_neg, ih, pow_succ, mul_neg_one]

/-- The ordered real sphere bounding a positive-dimensional complex
coordinate space has exactly the positive integral coordinate. -/
theorem orientedComplexBoundarySphere_coordinate (p : ℕ) :
    (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphereTopHomologyIso (2 * p)).hom (OrthantSphereCycle.orientedOrthantSphereClass (2 * p + 1)) = 1 := by
  rw [orientedOrthantSphereClass_coordinate, pow_mul]
  norm_num

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantCircleNormalization
