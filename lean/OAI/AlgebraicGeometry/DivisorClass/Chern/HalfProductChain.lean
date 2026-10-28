import OAI.AlgebraicGeometry.DivisorClass.Chern.PuncturedHalfSet
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HalfBoundaries

/-! # Half Product Chain -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HalfProductChain

noncomputable section

/-!
# ChernClass: the product boundary pieces as actual punctured chains

The outer arc is crossed with a tangent filling in its punctured
half-plane, and the half-disk is crossed with the punctured tangent
cycle. Both pieces are genuine chains in the common punctured product.
Forgetting that support gives exactly the previously computed chain.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem halfProductLeft_cross_inclusion (m : ℕ) (b : Bool) (p q n : ℕ) (h : p + q = n)
    (x : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).X p)
    (y : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X q) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b)).f n
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductLeftMap m b)).f n
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))
          (TopCat.of (EuclideanSpace ℝ (Fin m))) p q n h x y)) =
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b))
        (TopCat.of (EuclideanSpace ℝ (Fin m))) p q n h
        (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfBoundary.puncturedPlaneHalfInclusion b)).f p x) y := by
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  have hc : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductLeftMap m b) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((PuncturedHalfBoundary.puncturedPlaneHalfInclusion b, 𝟙 Y) :
          (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b), Y) ⟶ (TopCat.of (PlaneHalf.coordinatePlaneHalf b), Y))) := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have he := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hc)
    (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)) Y p q n h x y)
  refine he.trans ?_
  have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ (PuncturedHalfBoundary.puncturedPlaneHalfInclusion b) (𝟙 Y) p q n h x y
  rw [CategoryTheory.Functor.map_id] at hn
  exact hn

theorem halfProductRight_cross_inclusion (m : ℕ) (b : Bool) (p q n : ℕ) (h : p + q = n)
    (x : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X p)
    (y : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X q) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b)).f n
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductRightMap m b)).f n
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b))
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)))) p q n h x y)) =
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b))
        (TopCat.of (EuclideanSpace ℝ (Fin m))) p q n h x
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f q y) := by
  let X := TopCat.of (PlaneHalf.coordinatePlaneHalf b)
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y ({0}ᶜ)
  have hc : (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductRightMap m b) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 X, j) : (X, TopCat.of ({0}ᶜ : Set Y)) ⟶ (X, Y))) := by
    rw [← CategoryTheory.Functor.map_comp]
    rfl
  have he := ConcreteCategory.congr_hom (congrArg (fun f => f.f n) hc)
    (Singular.CrossBoundary.singularCrossChain ℚ X (TopCat.of ({0}ᶜ : Set Y)) p q n h x y)
  refine he.trans ?_
  have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ (𝟙 X) j p q n h x y
  rw [CategoryTheory.Functor.map_id] at hn
  exact hn

def halfProductPuncturedChain (m : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1)) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PuncturedHalfSet.PuncturedHalfProduct m b))).X (q + 3) :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductLeftMap m b)).f (q + 3)
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        1 (q + 2) (q + 3) (by omega) (Rational.HalfBoundaries.rationalPlaneHalfOuterPuncturedChain b) B) +
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductRightMap m b)).f (q + 3)
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b))
        (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))
        2 (q + 1) (q + 3) (by omega) (Rational.HalfBoundaries.rationalPlaneHalfFilling b) z)

theorem halfProductPuncturedChain_inclusion (m : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1)) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b)).f (q + 3)
      (halfProductPuncturedChain m b q B z) =
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
          1 (q + 2) (q + 3) (by omega) (Rational.HalfBoundaries.rationalPlaneHalfOuterChain b) B +
        Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
          2 (q + 1) (q + 3) (by omega) (Rational.HalfBoundaries.rationalPlaneHalfFilling b)
          ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) := by
  rw [halfProductPuncturedChain, map_add, halfProductLeft_cross_inclusion,
    halfProductRight_cross_inclusion, Rational.HalfBoundaries.rationalPlaneHalfOuterPuncturedChain_inclusion]

theorem halfProductPuncturedChain_boundary_inclusion (m : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z)
    (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).d
      (q + 1) q z = 0) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b)).f (q + 2)
        ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PuncturedHalfSet.PuncturedHalfProduct m b))).d (q + 3) (q + 2)
          (halfProductPuncturedChain m b q B z)) =
      (OrthantSphereEquator.orthantSign b : ℚ) •
        (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)))).d
          (q + 3) (q + 2)
          (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
            1 (q + 2) (q + 3) (by omega) (Rational.HalfBoundaries.rationalPlaneHalfAxisChain b) B) := by
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  let j := CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ Y ({0}ᶜ)
  have hj := ConcreteCategory.congr_hom (j.comm (q + 1) q) z
  change (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).d (q + 1) q (j.f (q + 1) z) =
    j.f q ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).d
      (q + 1) q z) at hj
  rw [hz, map_zero] at hj
  let f := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b)
  have hf := ConcreteCategory.congr_hom (f.comm (q + 3) (q + 2)) (halfProductPuncturedChain m b q B z)
  change (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)))).d
      (q + 3) (q + 2) (f.f (q + 3) (halfProductPuncturedChain m b q B z)) = _ at hf
  rw [show f.f (q + 3) (halfProductPuncturedChain m b q B z) = _ from
    halfProductPuncturedChain_inclusion m b q B z] at hf
  exact hf.symm.trans (Rational.HalfBoundaries.rationalPlaneHalfProduct_boundary b Y q B (j.f (q + 1) z) hB hj)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HalfProductChain
