import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.SphereAssemblyChains
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProductHalfBoundary

/-! # Product Sphere Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ProductSphereComparison

noncomputable section

/-! The boundary of the actual relative disk cross filling is the same
sphere class used in the two native Mayer–Vietoris calculations. -/

open _root_.CategoryTheory
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (m q : ℕ)
variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
variable (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
  (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
variable (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
  (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z)
variable (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
  (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).d (q + 1) q z = 0)

def fullPlaneProductSpherePieces : Rational.SphereAssembly.SphereRationalChainPieces m (q + 2) where
  left := ProductHalfBoundary.halfProductSphereChartChain m false q B z
  right := ProductHalfBoundary.halfProductSphereChartChain m true q B z
  overlap := ProductHalfBoundary.productAxisOverlapCycle m q B z hB
  left_boundary := by
    have h := ProductHalfBoundary.halfProductSphereChartChain_boundary m false q B z hB hz
    change _ = (-1 : ℚ) • _ at h
    rw [neg_one_smul] at h
    exact h
  right_boundary := by
    have h := ProductHalfBoundary.halfProductSphereChartChain_boundary m true q B z hB hz
    change _ = (1 : ℚ) • _ at h
    rw [one_smul] at h
    exact h

theorem fullPlaneProductSpherePieces_class :
    (fullPlaneProductSpherePieces m q B z hB hz).sphereClass =
      ProductHalfBoundary.halfProductSphereClass m q B z hB hz := rfl

theorem fullPlaneProductBoundaryChain_radial :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.fullPlaneProductRadialMap m)).f (q + 3)
      (PlaneProductTo.fullPlaneProductBoundaryChain m q B z) =
      (fullPlaneProductSpherePieces m q B z hB hz).ordinaryCycle.val := by
  rw [Rational.SphereAssembly.SphereRationalChainPieces.ordinaryCycle_val, PlaneProductTo.fullPlaneProductBoundaryChain, map_add]
  have hL := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.halfToFullProduct_radial m false)
  have hR := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.halfToFullProduct_radial m true)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hL hR
  exact congrArg₂ (fun x y => x + y)
    (ConcreteCategory.congr_hom (congrArg (fun f => f.f (q + 3)) hL)
      (HalfProductChain.halfProductPuncturedChain m false q B z))
    (ConcreteCategory.congr_hom (congrArg (fun f => f.f (q + 3)) hR)
      (HalfProductChain.halfProductPuncturedChain m true q B z))

theorem fullPlaneProductBoundaryCycle_radial :
    homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.fullPlaneProductRadialMap m)) (q + 3)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
        (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))))) (q + 3)
        (PlaneProductCycle.fullPlaneProductBoundaryCycle m q B z hB)) = ProductHalfBoundary.halfProductSphereClass m q B z hB hz := by
  let p := fullPlaneProductSpherePieces m q B z hB hz
  have hc : AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.fullPlaneProductRadialMap m)) (q + 3)
      (PlaneProductCycle.fullPlaneProductBoundaryCycle m q B z hB) = p.ordinaryCycle :=
    Subtype.ext (fullPlaneProductBoundaryChain_radial m q B z hB hz)
  erw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.fullPlaneProductRadialMap m))
    (q + 3) (PlaneProductCycle.fullPlaneProductBoundaryCycle m q B z hB)]
  rw [hc]
  exact p.sphereClass_eq_ordinaryCycle.symm.trans
    (fullPlaneProductSpherePieces_class m q B z hB hz)

theorem fullPlaneProductRelativeCycle_sphereBoundary :
    homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneProductTo.fullPlaneProductRadialMap m)) (q + 3)
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ
        (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).δ (q + 4) (q + 3) rfl
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ (q + 4) (PlaneProductCycle.fullPlaneProductRelativeCycle m q B z hB))) =
      ProductHalfBoundary.halfProductSphereClass m q B z hB hz := by
  rw [PlaneProductCycle.fullPlaneProductRelativeCycle_boundary, fullPlaneProductBoundaryCycle_radial m q B z hB hz]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ProductSphereComparison
