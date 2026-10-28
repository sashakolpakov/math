import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.AxisInterval

/-! # Product Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductBoundary

noncomputable section

/-!
# ChernClass: the axis-product boundary as an actual punctured chain

The endpoint product and interval–boundary product are supported off
the origin. Their difference is the ordinary boundary of the interval
product after inclusion in the full product space.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def axisProductPunctureInclusion (m : ℕ) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))) ⟶
      TopCat.of (ℝ × EuclideanSpace ℝ (Fin m)) :=
  CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (ℝ × EuclideanSpace ℝ (Fin m))) ({0}ᶜ)

theorem axisProductLeft_cross_inclusion (m p q n : ℕ) (h : p + q = n)
    (x : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ))).X p)
    (y : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X q) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisProductPunctureInclusion m)).f n
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductLeftPuncturedMap m)).f n
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ))
          (TopCat.of (EuclideanSpace ℝ (Fin m))) p q n h x y)) =
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) (TopCat.of (EuclideanSpace ℝ (Fin m))) p q n h
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of ℝ) ({0}ᶜ)).f p x) y := by
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of ℝ) ({0}ᶜ)
  have hc : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductLeftPuncturedMap m) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisProductPunctureInclusion m) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((j, 𝟙 Y) : (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ), Y) ⟶ (TopCat.of ℝ, Y))) := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have he := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hc)
    (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) Y p q n h x y)
  refine he.trans ?_
  have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ j (𝟙 Y) p q n h x y
  rw [CategoryTheory.Functor.map_id] at hn
  exact hn

theorem axisProductRight_cross_inclusion (m p q n : ℕ) (h : p + q = n)
    (x : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ℝ)).X p)
    (y : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X q) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisProductPunctureInclusion m)).f n
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductRightPuncturedMap m)).f n
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ)
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)))) p q n h x y)) =
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) (TopCat.of (EuclideanSpace ℝ (Fin m))) p q n h x
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f q y) := by
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y ({0}ᶜ)
  have hc : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductRightPuncturedMap m) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisProductPunctureInclusion m) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map
        ((𝟙 (TopCat.of ℝ), j) : (TopCat.of ℝ, TopCat.of ({0}ᶜ : Set Y)) ⟶ (TopCat.of ℝ, Y))) := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have he := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hc)
    (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) (TopCat.of ({0}ᶜ : Set Y)) p q n h x y)
  refine he.trans ?_
  have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ (𝟙 (TopCat.of ℝ)) j p q n h x y
  rw [CategoryTheory.Functor.map_id] at hn
  exact hn

def axisProductBoundaryChain (m q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1)) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))))).X (q + 2) :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductLeftPuncturedMap m)).f (q + 2)
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        0 (q + 2) (q + 2) (by omega) Rational.AxisInterval.rationalAxisPuncturedEndpointChain B) -
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductRightPuncturedMap m)).f (q + 2)
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))
        1 (q + 1) (q + 2) (by omega) Rational.AxisInterval.rationalAxisIntervalChain z)

theorem axisProductBoundaryChain_inclusion (m q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisProductPunctureInclusion m)).f (q + 2)
      (axisProductBoundaryChain m q B z) =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (ℝ × EuclideanSpace ℝ (Fin m)))).d (q + 3) (q + 2)
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) (TopCat.of (EuclideanSpace ℝ (Fin m)))
          1 (q + 2) (q + 3) (by omega) Rational.AxisInterval.rationalAxisIntervalChain B) := by
  rw [axisProductBoundaryChain, map_sub, axisProductLeft_cross_inclusion, axisProductRight_cross_inclusion]
  erw [Singular.CrossBoundary.singularCrossChain_boundary_interval_at ℚ (TopCat.of ℝ) (TopCat.of (EuclideanSpace ℝ (Fin m)))
      (q + 1) (q + 3) (q + 2) (by omega) (by omega), Rational.AxisInterval.rationalAxisIntervalChain_boundary, hB]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductBoundary
