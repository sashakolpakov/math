import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfAmbientChains
import OAI.AlgebraicGeometry.DivisorClass.Chern.SphereAssemblyChains
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProductHalfBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProductSecondMayerVietoris

/-! # Product Double Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ProductDoubleBoundary

noncomputable section

/-!
# ChernClass: the two native sphere boundaries recover the original tangent cycle

The half-interval assembly equals the actual axis-product sphere
class by equality of their ordinary chain representatives. Thus the
two previously computed negative signs cancel on the same classes.
-/

open _root_.CategoryTheory
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (r q : ℕ)
variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))).X (q + 2))
variable (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
  (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) (q + 1))
variable (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))).d
  (q + 2) (q + 1) B =
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin (r + 1)))) ({0}ᶜ)).f (q + 1) z.val)

theorem axisHalfSphereClass_eq_axisProduct :
    ProductSecondMayerVietoris.axisHalfSphereClass r q B z hB = ProductHalfBoundary.axisProductSphereClass (r + 1) q B z.val hB := by
  let p := ProductSecondMayerVietoris.axisHalfSpherePieces r q B z hB
  let f := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductEquator.axisProductRadialMap (r + 1))
  let a := Axis.ProductCycle.axisProductBoundaryCycle (r + 1) q B z.val hB
  have he : p.ordinaryCycle = AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap f (q + 2) a := by
    apply Subtype.ext
    exact p.ordinaryCycle_val.trans (Axis.HalfAmbientChains.axisHalfSphereChain_ambient_sum r q B z.val)
  calc
    ProductSecondMayerVietoris.axisHalfSphereClass r q B z hB =
        AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1))) (q + 2) p.ordinaryCycle :=
      p.sphereClass_eq_ordinaryCycle
    _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1))) (q + 2)
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap f (q + 2) a) := congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ _) he
    _ = ProductHalfBoundary.axisProductSphereClass (r + 1) q B z.val hB := (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality f (q + 2) a).symm

/-- The original rational Mayer–Vietoris boundary followed by the
specified ordered-equator retraction. -/
def rationalSphereLowerMap (m n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))).homology (n + 1) ⟶
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m)).homology n :=
  AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
    (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) n ≫
      homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (m + 1)).toFun)) n

theorem diskProductSphere_doubleBoundary :
    rationalSphereLowerMap r (q + 1)
      (rationalSphereLowerMap (r + 1) (q + 2)
        (ProductHalfBoundary.halfProductSphereClass (r + 1) q B z.val hB
          ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ q z.val).mp z.property))) =
      homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1)))))) (q + 1)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) (q + 1) z) := by
  have hz := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ q z.val).mp z.property
  have hfirst := ProductHalfBoundary.halfProductSphereClass_lowerSphere (r + 1) q B z.val hB hz
  change rationalSphereLowerMap (r + 1) (q + 2)
    (ProductHalfBoundary.halfProductSphereClass (r + 1) q B z.val hB hz) = -ProductHalfBoundary.axisProductSphereClass (r + 1) q B z.val hB at hfirst
  have hsecond := ProductSecondMayerVietoris.axisHalfSphereClass_lowerSphere r q B z hB
  change rationalSphereLowerMap r (q + 1) (ProductSecondMayerVietoris.axisHalfSphereClass r q B z hB) = _ at hsecond
  rw [hfirst, map_neg, ← axisHalfSphereClass_eq_axisProduct r q B z hB, hsecond, neg_neg]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ProductDoubleBoundary
