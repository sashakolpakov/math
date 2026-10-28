import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfChartNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductBoundary

/-! # Half Ambient Maps -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfAmbientMaps

noncomputable section

section

/-! The half-interval chart maps are the restrictions of the original axis-product radial map. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def axisHalfPuncturedToReal (b : Bool) : TopCat.of (Half.PuncturedAxisHalf b) ⟶ TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ) :=
  TopCat.ofHom ⟨fun x => ⟨x.val.val, x.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem axisHalfEndpointPunctured_map (b : Bool) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisHalfPuncturedToReal b)).f 0
      (Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (Half.PuncturedAxisHalf b)) (HalfChartNaturality.axisHalfEndpointPunctured b)) =
      Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) (Rational.AxisInterval.realAxisPuncturedPoint (fun _ => b)) :=
  Singular.CrossBoundary.scalarPointChain_map ℚ (axisHalfPuncturedToReal b) (HalfChartNaturality.axisHalfEndpointPunctured b)

theorem axisHalfLeftChart_ambient (m : ℕ) (b : Bool) :
    TopCat.ofHom (Half.axisHalfLeftChartMap m b) ≫
        CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (Half.axisProductPole m b)) =
      AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((axisHalfPuncturedToReal b, 𝟙 (TopCat.of (EuclideanSpace ℝ (Fin m)))) :
        (TopCat.of (Half.PuncturedAxisHalf b), TopCat.of (EuclideanSpace ℝ (Fin m))) ⟶
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ), TopCat.of (EuclideanSpace ℝ (Fin m)))) ≫
        HalfProductMaps.axisProductLeftPuncturedMap m ≫ ProductEquator.axisProductRadialMap m := rfl

theorem axisHalfRightChart_ambient (m : ℕ) (b : Bool) :
    TopCat.ofHom (Half.axisHalfRightChartMap m b) ≫
        CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (Half.axisProductPole m b)) =
      AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((HalfChains.axisHalfInclusion b, 𝟙 (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))) :
        (TopCat.of (Half.axisHalfLine b), TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)))) ⟶
          (TopCat.of ℝ, TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))) ≫
        HalfProductMaps.axisProductRightPuncturedMap m ≫ ProductEquator.axisProductRadialMap m := rfl

theorem realAxisPuncturedEndpointChain_split :
    Rational.AxisInterval.realAxisPuncturedEndpointChain =
      AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)))
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ))).symm (Rational.AxisInterval.realAxisPuncturedPoint (fun _ => true))) -
        AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)))
          ((TopCat.toSSetObj₀Equiv (X := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ))).symm (Rational.AxisInterval.realAxisPuncturedPoint (fun _ => false))) := by
  rw [Rational.AxisInterval.realAxisPuncturedEndpointChain, OrthantBoundaryRepresentatives.sum_orthant_head_tail]
  simp only [Fintype.sum_unique]
  have hw (b : Bool) : OrthantSphereEquator.orthantWeight (Fin.cons b (default : Fin 0 → Bool)) = OrthantSphereEquator.orthantSign b := by
    rw [OrthantSphereEquator.orthantWeight_cons]
    simp [OrthantSphereEquator.orthantWeight]
  erw [hw, hw]
  change (-1 : ℤ) • _ + (1 : ℤ) • _ = _
  erw [neg_one_zsmul, one_zsmul, add_comm, sub_eq_add_neg]
  rfl

theorem rationalAxisPuncturedEndpointChain_split :
    Rational.AxisInterval.rationalAxisPuncturedEndpointChain =
      Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) (Rational.AxisInterval.realAxisPuncturedPoint (fun _ => true)) -
        Singular.CrossBoundary.scalarPointChain ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) (Rational.AxisInterval.realAxisPuncturedPoint (fun _ => false)) := by
  rw [Rational.AxisInterval.rationalAxisPuncturedEndpointChain, realAxisPuncturedEndpointChain_split,
    Rational.ChainRepresentatives.rationalSingularChainElement_sub, HalfChains.rationalSingularChainElement_simplex,
    HalfChains.rationalSingularChainElement_simplex]
  rfl

end

/-! The endpoint-product comparison as an equality of the original chain maps. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem axisHalfEndpointProduct_comparison (m : ℕ) (b : Bool) :
    Singular.CrossBoundary.singularPointCross ℚ (TopCat.of (Half.PuncturedAxisHalf b)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        (HalfChartNaturality.axisHalfEndpointPunctured b) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (Half.axisHalfLeftChartMap m b)) ≫
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (Half.axisProductPole m b))) =
      Singular.CrossBoundary.singularPointCross ℚ (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
          (Rational.AxisInterval.realAxisPuncturedPoint (fun _ => b)) ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (HalfProductMaps.axisProductLeftPuncturedMap m) ≫
        (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (ProductEquator.axisProductRadialMap m) := by
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  have hn := Singular.CrossBoundary.singularPointCross_naturality ℚ (axisHalfPuncturedToReal b) (𝟙 Y) (HalfChartNaturality.axisHalfEndpointPunctured b)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  rw [← CategoryTheory.Functor.map_comp, axisHalfLeftChart_ambient,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← Category.assoc, hn]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfAmbientMaps
