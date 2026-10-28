import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ProductCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.HalfProductChain
import OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris

/-! # Product Half Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ProductHalfBoundary

noncomputable section

section

/-!
# ChernClass: each punctured half-product has the signed shared axis boundary

Injectivity of the genuine subspace chain inclusion transports the
proved full-product boundary identity to the punctured supports.
Both half-products use the same explicit axis cycle.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem axisHalfProductMap_ambient (m : ℕ) (b : Bool) :
    Axis.HalfProductMaps.axisHalfProductMap m b ≫ PuncturedHalfSet.halfProductPunctureInclusion m b =
      Axis.ProductBoundary.axisProductPunctureInclusion m ≫ AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map
        ((Axis.Half.axisPlaneHalfInclusion b, 𝟙 (TopCat.of (EuclideanSpace ℝ (Fin m)))) :
          (TopCat.of ℝ, TopCat.of (EuclideanSpace ℝ (Fin m))) ⟶
            (TopCat.of (PlaneHalf.coordinatePlaneHalf b), TopCat.of (EuclideanSpace ℝ (Fin m)))) := rfl

theorem axisProductBoundaryChain_half_ambient (m : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b)).f (q + 2)
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.HalfProductMaps.axisHalfProductMap m b)).f (q + 2)
        (Axis.ProductBoundary.axisProductBoundaryChain m q B z)) =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)))).d
        (q + 3) (q + 2)
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) (TopCat.of (EuclideanSpace ℝ (Fin m)))
          1 (q + 2) (q + 3) (by omega) (Rational.HalfBoundaries.rationalPlaneHalfAxisChain b) B) := by
  let Y := TopCat.of (EuclideanSpace ℝ (Fin m))
  let g := AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((Axis.Half.axisPlaneHalfInclusion b, 𝟙 Y) :
    (TopCat.of ℝ, Y) ⟶ (TopCat.of (PlaneHalf.coordinatePlaneHalf b), Y))
  let f := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map g
  have hcomp := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (axisHalfProductMap_ambient m b)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hcomp
  have he := ConcreteCategory.congr_hom (congrArg (fun u => u.f (q + 2)) hcomp)
    (Axis.ProductBoundary.axisProductBoundaryChain m q B z)
  change _ = f.f (q + 2)
    (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductBoundary.axisProductPunctureInclusion m)).f (q + 2)
      (Axis.ProductBoundary.axisProductBoundaryChain m q B z)) at he
  rw [Axis.ProductBoundary.axisProductBoundaryChain_inclusion m q B z hB] at he
  have hc : f.f (q + 3)
      (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) Y 1 (q + 2) (q + 3) (by omega) Rational.AxisInterval.rationalAxisIntervalChain B) =
    Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) Y 1 (q + 2) (q + 3) (by omega)
      (Rational.HalfBoundaries.rationalPlaneHalfAxisChain b) B := by
    have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ (Axis.Half.axisPlaneHalfInclusion b) (𝟙 Y)
      1 (q + 2) (q + 3) (by omega) Rational.AxisInterval.rationalAxisIntervalChain B
    rw [CategoryTheory.Functor.map_id, Rational.AxisInterval.rationalAxisIntervalChain_half_inclusion] at hn
    exact hn
  have hd := ConcreteCategory.congr_hom (f.comm (q + 3) (q + 2))
    (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of ℝ) Y 1 (q + 2) (q + 3) (by omega) Rational.AxisInterval.rationalAxisIntervalChain B)
  change (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)))).d
      (q + 3) (q + 2) (f.f (q + 3) _) = _ at hd
  rw [hc] at hd
  exact he.trans hd.symm

theorem halfProductPuncturedChain_axis_boundary (m : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z)
    (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).d
      (q + 1) q z = 0) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PuncturedHalfSet.PuncturedHalfProduct m b))).d (q + 3) (q + 2)
        (HalfProductChain.halfProductPuncturedChain m b q B z) =
      (OrthantSphereEquator.orthantSign b : ℚ) • ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.HalfProductMaps.axisHalfProductMap m b)).f (q + 2)
        (Axis.ProductBoundary.axisProductBoundaryChain m q B z) := by
  apply PuncturedHalfSet.halfProductPuncture_chain_injective ℚ m b (q + 2)
  rw [map_smul, HalfProductChain.halfProductPuncturedChain_boundary_inclusion m b q B z hB hz,
    axisProductBoundaryChain_half_ambient m b q B z hB]

end

section

/-! Exact boundaries of the half-product chains in the actual sphere pole charts. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def halfProductSphereChartChain (m : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1)) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (PlaneProductCharts.planeProductPole m b)))).X (q + 3) :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductChartMap m b)).f (q + 3)
    (HalfProductChain.halfProductPuncturedChain m b q B z)

def axisProductOverlapChain (m q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1)) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)) ∩
        CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)) : Set (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))))).X (q + 2) :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductEquator.planeAxisProductOverlap m)).f (q + 2)
    (Axis.ProductBoundary.axisProductBoundaryChain m q B z)

theorem halfProductSphereChartChain_boundary (m : ℕ) (b : Bool) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z)
    (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).d
      (q + 1) q z = 0) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (PlaneProductCharts.planeProductPole m b)))).d
        (q + 3) (q + 2) (halfProductSphereChartChain m b q B z) =
      (OrthantSphereEquator.orthantSign b : ℚ) • ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.HalfProductMaps.planeProductOverlapToChart m b)).f (q + 2)
        (axisProductOverlapChain m q B z) := by
  let f := (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductChartMap m b)
  have hf := ConcreteCategory.congr_hom (f.comm (q + 3) (q + 2)) (HalfProductChain.halfProductPuncturedChain m b q B z)
  change _ = f.f (q + 2)
    ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PuncturedHalfSet.PuncturedHalfProduct m b))).d (q + 3) (q + 2)
      (HalfProductChain.halfProductPuncturedChain m b q B z)) at hf
  rw [halfProductPuncturedChain_axis_boundary m b q B z hB hz, map_smul] at hf
  have hc := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.HalfProductMaps.axisHalfProductMap_chart m b)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hc
  have he := ConcreteCategory.congr_hom (congrArg (fun g => g.f (q + 2)) hc) (Axis.ProductBoundary.axisProductBoundaryChain m q B z)
  exact hf.trans (congrArg (fun x => (OrthantSphereEquator.orthantSign b : ℚ) • x) he)

end

/-!
# ChernClass: the first native Mayer–Vietoris boundary of the disk product

The actual two chart chains have opposite axis boundaries. The native
small-chain exact sequence therefore sends their assembled sphere
class to the negative of the specified axis-product cycle.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (m q : ℕ)

local notation "CU" => OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantFirstChart m)
local notation "CV" => OAI.AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantSecondChart m)
local notation "S" => OAI.AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence (OAI.AlgebraicGeometry.CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
  (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1))) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
local notation "jU" => CategoryTheory.Functor.map (OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion m)
local notation "jV" => CategoryTheory.Functor.map (OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ) (OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion m)

variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
variable (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))
variable (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
  (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z)
variable (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).d
  (q + 1) q z = 0)

def productAxisOverlapCycle :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap m)) (q + 2) :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductEquator.planeAxisProductOverlap m)) (q + 2)
    (Axis.ProductCycle.axisProductBoundaryCycle m q B z hB)

theorem productAxisOverlapCycle_val :
    (productAxisOverlapCycle m q B z hB).val = axisProductOverlapChain m q B z := rfl

def halfProductSphereMiddleChain : (S).X₂.X (q + 3) :=
  (biprod.inl : CU ⟶ CU ⊞ CV).f (q + 3) (halfProductSphereChartChain m false q B z) +
    (biprod.inr : CV ⟶ CU ⊞ CV).f (q + 3) (halfProductSphereChartChain m true q B z)

include hB hz in
theorem halfProductSphereMiddleChain_boundary :
    (S).f.f (q + 2) (-(axisProductOverlapChain m q B z)) =
      (S).X₂.d (q + 3) (q + 2) (halfProductSphereMiddleChain m q B z) := by
  have hu : (jU).f (q + 2) (-(axisProductOverlapChain m q B z)) =
      (CU).d (q + 3) (q + 2) (halfProductSphereChartChain m false q B z) := by
    have h := halfProductSphereChartChain_boundary m false q B z hB hz
    change (CU).d (q + 3) (q + 2) (halfProductSphereChartChain m false q B z) =
      (-1 : ℚ) • (jU).f (q + 2) (axisProductOverlapChain m q B z) at h
    rw [neg_one_smul] at h
    rw [map_neg]
    exact h.symm
  have hv : (jV).f (q + 2) (-(axisProductOverlapChain m q B z)) =
      -((CV).d (q + 3) (q + 2) (halfProductSphereChartChain m true q B z)) := by
    have h := halfProductSphereChartChain_boundary m true q B z hB hz
    change (CV).d (q + 3) (q + 2) (halfProductSphereChartChain m true q B z) =
      (1 : ℚ) • (jV).f (q + 2) (axisProductOverlapChain m q B z) at h
    rw [one_smul] at h
    rw [map_neg, h]
  have hf : (S).f = (jU) ≫ (biprod.inl : CU ⟶ CU ⊞ CV) -
      (jV) ≫ (biprod.inr : CV ⟶ CU ⊞ CV) := by
    simp only [AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalSmallMayerVietorisSequence_f, biprod.lift_eq, Preadditive.neg_comp,
      sub_eq_add_neg, OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion, OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion]
    rfl
  have hl := ConcreteCategory.congr_hom ((biprod.inl : CU ⟶ CU ⊞ CV).comm (q + 3) (q + 2))
    (halfProductSphereChartChain m false q B z)
  have hr := ConcreteCategory.congr_hom ((biprod.inr : CV ⟶ CU ⊞ CV).comm (q + 3) (q + 2))
    (halfProductSphereChartChain m true q B z)
  change (CU ⊞ CV).d (q + 3) (q + 2) ((biprod.inl : CU ⟶ CU ⊞ CV).f (q + 3) _) =
    (biprod.inl : CU ⟶ CU ⊞ CV).f (q + 2) ((CU).d (q + 3) (q + 2) _) at hl
  change (CU ⊞ CV).d (q + 3) (q + 2) ((biprod.inr : CV ⟶ CU ⊞ CV).f (q + 3) _) =
    (biprod.inr : CV ⟶ CU ⊞ CV).f (q + 2) ((CV).d (q + 3) (q + 2) _) at hr
  change (S).f.f (q + 2) (-(axisProductOverlapChain m q B z)) =
    (CU ⊞ CV).d (q + 3) (q + 2) (halfProductSphereMiddleChain m q B z)
  rw [halfProductSphereMiddleChain, map_add, hl, hr, hf]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.comp_f,
    ModuleCat.hom_sub, LinearMap.sub_apply, ConcreteCategory.comp_apply]
  have hL := congrArg (fun x : (CU).X (q + 2) => (biprod.inl : CU ⟶ CU ⊞ CV).f (q + 2) x) hu
  have hR := congrArg (fun x : (CV).X (q + 2) => (biprod.inr : CV ⟶ CU ⊞ CV).f (q + 2) x) hv
  refine (congrArg₂ (fun x y : (CU ⊞ CV).X (q + 2) => x - y) hL hR).trans ?_
  rw [map_neg, sub_neg_eq_add]

def halfProductSphereSmallCycle : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (S).X₃ (q + 3) :=
  ⟨(S).g.f (q + 3) (halfProductSphereMiddleChain m q B z), by
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ]
    have h := ConcreteCategory.congr_hom ((S).g.comm (q + 3) (q + 2)) (halfProductSphereMiddleChain m q B z)
    change (S).X₃.d (q + 3) (q + 2) ((S).g.f (q + 3) _) =
      (S).g.f (q + 2) ((S).X₂.d (q + 3) (q + 2) (halfProductSphereMiddleChain m q B z)) at h
    rw [← halfProductSphereMiddleChain_boundary m q B z hB hz] at h
    exact h.trans (ConcreteCategory.congr_hom
      (congrArg (fun f => f.f (q + 2)) (S).zero) (-(axisProductOverlapChain m q B z)))⟩

def halfProductSphereClass : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))).homology (q + 3) :=
  HomologicalComplex.homologyMap (AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.binarySmallRationalChainInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))) (q + 3)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (S).X₃ (q + 3) (halfProductSphereSmallCycle m q B z hB hz))

theorem halfProductSphereClass_firstBoundary :
    AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) (q + 2)
      (halfProductSphereClass m q B z hB hz) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap m)) (q + 2)
        (-(productAxisOverlapCycle m q B z hB)) := by
  apply AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary_eq_of_lift (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
    (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
    (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) (q + 2)
    (halfProductSphereSmallCycle m q B z hB hz) (halfProductSphereMiddleChain m q B z)
    (-(productAxisOverlapCycle m q B z hB)) rfl
  exact halfProductSphereMiddleChain_boundary m q B z hB hz

def axisProductSphereClass : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere m)).homology (q + 2) :=
  HomologicalComplex.homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductEquator.axisProductRadialMap m)) (q + 2)
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))))) (q + 2)
      (Axis.ProductCycle.axisProductBoundaryCycle m q B z hB))

theorem halfProductSphereClass_lowerSphere :
    HomologicalComplex.homologyMap
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (m + 1)).toFun)) (q + 2)
      (AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1))
        (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
        (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (m + 1)))
        (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) (q + 2)
        (halfProductSphereClass m q B z hB hz)) = -axisProductSphereClass m q B z hB := by
  rw [halfProductSphereClass_firstBoundary, map_neg, map_neg]
  apply congrArg Neg.neg
  have hc := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductEquator.planeAxisProductOverlap m)) (q + 2)
    (Axis.ProductCycle.axisProductBoundaryCycle m q B z hB)
  change _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap m)) (q + 2)
    (productAxisOverlapCycle m q B z hB) at hc
  rw [← hc]
  have hm : HomologicalComplex.homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductEquator.planeAxisProductOverlap m)) (q + 2) ≫
      HomologicalComplex.homologyMap
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (m + 1)).toFun)) (q + 2) =
      HomologicalComplex.homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (Axis.ProductEquator.axisProductRadialMap m)) (q + 2) := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
      Axis.ProductEquator.planeAxisProductOverlap_retraction]
  exact ConcreteCategory.congr_hom hm
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (ℝ × EuclideanSpace ℝ (Fin m))))) (q + 2)
      (Axis.ProductCycle.axisProductBoundaryCycle m q B z hB))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ProductHalfBoundary
