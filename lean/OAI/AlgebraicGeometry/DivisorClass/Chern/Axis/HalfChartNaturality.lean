import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChains
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ZeroEquator

/-! # Half Chart Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChartNaturality

noncomputable section

/-! The two support maps of an axis half-product agree on their common punctured domain. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def axisHalfPunctureInclusion (b : Bool) : TopCat.of (Half.PuncturedAxisHalf b) ⟶ TopCat.of (Half.axisHalfLine b) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def axisHalfEndpointPunctured (b : Bool) : Half.PuncturedAxisHalf b :=
  ⟨Half.axisHalfEndpoint b, by
    intro h
    change (OrthantSphereEquator.orthantSign b : ℝ) = 0 at h
    exact OrthantSphereEquator.orthantSign_ne_zero b (by exact_mod_cast h)⟩

theorem axisHalfChart_cross_overlap (m : ℕ) (b : Bool) (p q n : ℕ) (h : p + q = n)
    (x : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (Half.PuncturedAxisHalf b))).X p)
    (y : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X q) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfLeftChartMap m b))).f n
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (Half.PuncturedAxisHalf b)) (TopCat.of (EuclideanSpace ℝ (Fin m))) p q n h x
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f q y)) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap m b))).f n
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (Half.axisHalfLine b))
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)))) p q n h
          (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisHalfPunctureInclusion b)).f p x) y) := by
  let X := TopCat.of (Half.PuncturedAxisHalf b)
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  let A := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)))
  let j := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion Y ({0}ᶜ)
  let f := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((𝟙 X, j) : (X, A) ⟶ (X, Y))
  let g := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((axisHalfPunctureInclusion b, 𝟙 A) : (X, A) ⟶ (TopCat.of (Half.axisHalfLine b), A))
  have hl := Singular.CrossBoundary.singularCrossChain_naturality ℚ (𝟙 X) j p q n h x y
  rw [CategoryTheory.Functor.map_id] at hl
  have hr := Singular.CrossBoundary.singularCrossChain_naturality ℚ (axisHalfPunctureInclusion b) (𝟙 A) p q n h x y
  rw [CategoryTheory.Functor.map_id] at hr
  have hc : f ≫ TopCat.ofHom (Half.axisHalfLeftChartMap m b) =
      g ≫ TopCat.ofHom (Half.axisHalfRightChartMap m b) := rfl
  have hmap := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map hc
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hmap
  have he := ConcreteCategory.congr_hom (congrArg (fun u => u.f n) hmap)
    (Singular.CrossBoundary.singularCrossChain ℚ X A p q n h x y)
  change ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfLeftChartMap m b))).f n
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f).f n _) =
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap m b))).f n
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map g).f n _) at he
  rw [show ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f).f n _ = _ from hl,
    show ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map g).f n _ = _ from hr] at he
  exact he

def axisZeroOverlapChain (r n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))).X n) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap r)).X n :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ZeroEquator.axisZeroProductOverlap r)).f n
    (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of Unit)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))) 0 n n (by omega)
      (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of Unit) ()) z)

theorem axisHalfZeroChart_cross (r : ℕ) (b : Bool) (n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))).X n) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b))).f n
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (Half.axisHalfLine b))
        (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))) 0 n n (by omega)
        (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Half.axisHalfLine b)) (Half.axisHalfOrigin b)) z) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.planeProductOverlapToChart r b)).f n (axisZeroOverlapChain r n z) := by
  let Y := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1))))
  have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ (ZeroEquator.axisHalfZeroPointMap b) (𝟙 Y) 0 n n (by omega)
    (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of Unit) ()) z
  rw [CategoryTheory.Functor.map_id, Singular.CrossBoundary.scalarPointChain_map] at hn
  have hc := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ZeroEquator.axisHalfZeroProduct_chart r b)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hc
  have he := ConcreteCategory.congr_hom (congrArg (fun u => u.f n) hc)
    (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of Unit) Y 0 n n (by omega) (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of Unit) ()) z)
  change ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfRightChartMap (r + 1) b))).f n
    (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ZeroEquator.axisHalfZeroProductMap r b)).f n _) = _ at he
  rw [show ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ZeroEquator.axisHalfZeroProductMap r b)).f n _ = _ from hn] at he
  exact he

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChartNaturality
