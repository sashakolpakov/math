import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfProductMaps
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HalfBoundaries

/-! # Axis Interval -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.AxisInterval

noncomputable section

/-! Rational axis chains with genuine punctured endpoints and the prescribed half-plane images. -/

open _root_.CategoryTheory
open scoped Simplicial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def realAxisPuncturedPoint (η : Fin 1 → Bool) : CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ :=
  ⟨(OrthantSphereEquator.orthantSign (η 0) : ℝ), by
    intro h
    change (OrthantSphereEquator.orthantSign (η 0) : ℝ) = 0 at h
    exact OrthantSphereEquator.orthantSign_ne_zero (η 0) (by exact_mod_cast h)⟩

def realAxisPuncturedEndpointChain : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ))).X 0 :=
  ∑ η : Fin 1 → Bool, OrthantSphereEquator.orthantWeight η • AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ)
    (TopCat.toSSet.obj (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)))
    ((TopCat.toSSetObj₀Equiv (X := TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ))).symm (realAxisPuncturedPoint η))

theorem realAxisPuncturedEndpointChain_inclusion :
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion (TopCat.of ℝ) ({0}ᶜ)).f 0 realAxisPuncturedEndpointChain =
      Axis.Half.realAxisEndpointChain := by
  rw [realAxisPuncturedEndpointChain, Axis.Half.realAxisEndpointChain, map_sum]
  apply Finset.sum_congr rfl
  intro η _
  rw [map_zsmul, OrthantBoundaryRepresentatives.integralSimplexChain_map]
  rfl

def rationalAxisIntervalChain : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ℝ)).X 1 :=
  ChainRepresentatives.rationalSingularChainElement (TopCat.of ℝ) 1 Axis.Half.realAxisIntervalChain

def rationalAxisPuncturedEndpointChain :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ))).X 0 :=
  ChainRepresentatives.rationalSingularChainElement (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ)) 0 realAxisPuncturedEndpointChain

theorem rationalAxisIntervalChain_boundary :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of ℝ)).d 1 0 rationalAxisIntervalChain =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of ℝ) ({0}ᶜ)).f 0 rationalAxisPuncturedEndpointChain := by
  rw [rationalAxisIntervalChain, ChainRepresentatives.rationalSingularChainElement_d, Axis.Half.realAxisIntervalChain_boundary,
    rationalAxisPuncturedEndpointChain]
  refine (congrArg (ChainRepresentatives.rationalSingularChainElement (TopCat.of ℝ) 0)
    realAxisPuncturedEndpointChain_inclusion).symm.trans ?_
  exact (ChainRepresentatives.rationalSingularChainElement_map (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of ℝ) ({0}ᶜ)) 0
    realAxisPuncturedEndpointChain).symm

theorem rationalAxisIntervalChain_half_inclusion (b : Bool) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.Half.axisPlaneHalfInclusion b)).f 1 rationalAxisIntervalChain =
      HalfBoundaries.rationalPlaneHalfAxisChain b := by
  rw [rationalAxisIntervalChain, ChainRepresentatives.rationalSingularChainElement_map, Axis.Half.realAxisIntervalChain_half_inclusion]
  rfl

def axisPuncturedPlaneHalfInclusion (b : Bool) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ) ⟶ TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b) :=
  TopCat.ofHom ⟨fun p => ⟨Axis.Half.axisPlaneHalfInclusion b p.val, by
      intro h
      exact p.property (congrArg (fun x : PlaneHalf.CoordinatePlane => x 1) h)⟩,
    ((Axis.Half.axisPlaneHalfInclusion b).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem axisHalfProductMap_left (m : ℕ) (b : Bool) :
    Axis.HalfProductMaps.axisProductLeftPuncturedMap m ≫ Axis.HalfProductMaps.axisHalfProductMap m b =
      AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map
          ((axisPuncturedPlaneHalfInclusion b, 𝟙 (TopCat.of (EuclideanSpace ℝ (Fin m)))) :
            (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal ℝ), TopCat.of (EuclideanSpace ℝ (Fin m))) ⟶
              (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b), TopCat.of (EuclideanSpace ℝ (Fin m)))) ≫
        PuncturedHalfSet.halfProductLeftMap m b := rfl

theorem axisHalfProductMap_right (m : ℕ) (b : Bool) :
    Axis.HalfProductMaps.axisProductRightPuncturedMap m ≫ Axis.HalfProductMaps.axisHalfProductMap m b =
      AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map
          ((Axis.Half.axisPlaneHalfInclusion b, 𝟙 (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))) :
            (TopCat.of ℝ, TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m)))) ⟶
              (TopCat.of (PlaneHalf.coordinatePlaneHalf b), TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))) ≫
        PuncturedHalfSet.halfProductRightMap m b := rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.AxisInterval
