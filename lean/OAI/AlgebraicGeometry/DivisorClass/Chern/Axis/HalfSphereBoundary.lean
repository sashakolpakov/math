import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChartNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.MappedCrossBoundary

/-! # Half Sphere Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfSphereBoundary

noncomputable section

/-!
# ChernClass: the second sphere-cover boundary on the actual axis half-products

For each half-interval, the endpoint–boundary terms cancel. The
remaining boundary is the signed product of the zero point with the
tangent cycle, mapped through the actual ordered equator.
-/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (r : ℕ) (b : Bool) (q : ℕ)

local notation "Y" => TopCat.of (EuclideanSpace ℝ (Fin (r + 1)))
local notation "A" => TopCat.of (OAI.AlgebraicGeometry.CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))
local notation "H" => TopCat.of (OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half.axisHalfLine b)
local notation "P" => TopCat.of (OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half.PuncturedAxisHalf b)
local notation "Z" => TopCat.of (OAI.AlgebraicGeometry.CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.Half.axisProductPole (r + 1) b))

variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))).X (q + 2))
variable (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))).X (q + 1))

def axisHalfEndpointProductChain : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Z).X (q + 2) :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfLeftChartMap (r + 1) b))).f (q + 2)
    (Singular.CrossBoundary.singularCrossChain ℚ P Y 0 (q + 2) (q + 2) (by omega)
      (Singular.CrossBoundary.scalarPointChain ℚ P (HalfChartNaturality.axisHalfEndpointPunctured b)) B)

def axisHalfRayProductChain : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Z).X (q + 2) :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b))).f (q + 2)
    (Singular.CrossBoundary.singularCrossChain ℚ H A 1 (q + 1) (q + 2) (by omega) (HalfChains.rationalAxisHalfRayChain b) z)

def axisHalfSphereChain : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Z).X (q + 2) :=
  (OrthantSphereEquator.orthantSign b : ℚ) • (axisHalfEndpointProductChain r b q B - axisHalfRayProductChain r b q z)

theorem axisHalfEndpointProductChain_boundary
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ Y ({0}ᶜ)).f (q + 1) z) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Z).d (q + 2) (q + 1) (axisHalfEndpointProductChain r b q B) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b))).f (q + 1)
        (Singular.CrossBoundary.singularCrossChain ℚ H A 0 (q + 1) (q + 1) (by omega)
          (Singular.CrossBoundary.scalarPointChain ℚ H (Half.axisHalfEndpoint b)) z) := by
  unfold axisHalfEndpointProductChain
  erw [MappedCrossBoundary.mappedCross_boundary_point ℚ P Y Z (TopCat.ofHom (Half.axisHalfLeftChartMap (r + 1) b)) (q + 1), hB,
    HalfChartNaturality.axisHalfChart_cross_overlap, Singular.CrossBoundary.scalarPointChain_map]
  rfl

theorem axisHalfRayProductChain_boundary
    (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) A).d (q + 1) q z = 0) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Z).d (q + 2) (q + 1) (axisHalfRayProductChain r b q z) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b))).f (q + 1)
          (Singular.CrossBoundary.singularCrossChain ℚ H A 0 (q + 1) (q + 1) (by omega)
            (Singular.CrossBoundary.scalarPointChain ℚ H (Half.axisHalfEndpoint b)) z) -
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b))).f (q + 1)
          (Singular.CrossBoundary.singularCrossChain ℚ H A 0 (q + 1) (q + 1) (by omega)
            (Singular.CrossBoundary.scalarPointChain ℚ H (Half.axisHalfOrigin b)) z) := by
  unfold axisHalfRayProductChain
  erw [MappedCrossBoundary.mappedCross_boundary_interval ℚ H A Z (TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b))
    q (q + 2) (q + 1) (by omega) (by omega), HalfChains.rationalAxisHalfRayChain_boundary, hz,
    Singular.CrossBoundary.singularCrossChain_zero_right, sub_zero, Singular.CrossBoundary.singularCrossChain_sub_left, map_sub]

theorem axisHalfSphereChain_boundary
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ Y ({0}ᶜ)).f (q + 1) z)
    (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) A).d (q + 1) q z = 0) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Z).d (q + 2) (q + 1) (axisHalfSphereChain r b q B z) =
      (OrthantSphereEquator.orthantSign b : ℚ) • ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.planeProductOverlapToChart r b)).f (q + 1)
        (HalfChartNaturality.axisZeroOverlapChain r (q + 1) z) := by
  rw [axisHalfSphereChain, map_smul, map_sub, axisHalfEndpointProductChain_boundary r b q B z hB,
    axisHalfRayProductChain_boundary r b q z hz, sub_sub_cancel, HalfChartNaturality.axisHalfZeroChart_cross]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfSphereBoundary
