import OAI.AlgebraicGeometry.DivisorClass.Chern.HalfProductChain
import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneDiskBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrderedRadialNaturality

/-! # Plane Product To -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductTo

noncomputable section

section

/-! The actual punctured full product receiving both supported half-products. -/

open _root_.CategoryTheory OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def halfToFullProductMap (m : ℕ) (b : Bool) :
    TopCat.of (PlaneHalf.coordinatePlaneHalf b × EuclideanSpace ℝ (Fin m)) ⟶
      TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m)) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((PlaneDiskBoundary.planeHalfInclusion b, 𝟙 (TopCat.of (EuclideanSpace ℝ (Fin m)))) :
    (TopCat.of (PlaneHalf.coordinatePlaneHalf b), TopCat.of (EuclideanSpace ℝ (Fin m))) ⟶
      (TopCat.of PlaneHalf.CoordinatePlane, TopCat.of (EuclideanSpace ℝ (Fin m))))

def halfToFullPuncturedProductMap (m : ℕ) (b : Bool) :
    TopCat.of (PuncturedHalfSet.PuncturedHalfProduct m b) ⟶
      TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) :=
  TopCat.ofHom ⟨fun p => ⟨(p.val.1.val, p.val.2), p.property⟩,
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

def fullPlaneProductRadialMap (m : ℕ) :
    TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ⟶
      CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1) :=
  TopCat.ofHom ((CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (m + 2)))).comp
    ⟨CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (PlaneProductCharts.planeProductCoordinates m),
      (CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (PlaneProductCharts.planeProductCoordinates m)).continuous⟩)

theorem halfToFullProduct_inclusion (m : ℕ) (b : Bool) :
    halfToFullPuncturedProductMap m b ≫
      CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ) =
      PuncturedHalfSet.halfProductPunctureInclusion m b ≫ halfToFullProductMap m b := rfl

theorem halfToFullProduct_radial (m : ℕ) (b : Bool) :
    halfToFullPuncturedProductMap m b ≫ fullPlaneProductRadialMap m =
      PuncturedHalfSet.halfProductChartMap m b ≫
        CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (m + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (PlaneProductCharts.planeProductPole m b)) := rfl

end

section

/-! Coefficient change preserves the actual two-half-disk decomposition. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rationalPlaneDiskFilling : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of PlaneHalf.CoordinatePlane)).X 2 :=
  Rational.ChainRepresentatives.rationalSingularChainElement (TopCat.of PlaneHalf.CoordinatePlane) 2 PlaneDiskBoundary.planeDiskFilling

theorem rationalPlaneHalfFilling_sum :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneDiskBoundary.planeHalfInclusion false)).f 2 (Rational.HalfBoundaries.rationalPlaneHalfFilling false) +
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneDiskBoundary.planeHalfInclusion true)).f 2 (Rational.HalfBoundaries.rationalPlaneHalfFilling true) =
      rationalPlaneDiskFilling := by
  unfold Rational.HalfBoundaries.rationalPlaneHalfFilling rationalPlaneDiskFilling
  rw [Rational.ChainRepresentatives.rationalSingularChainElement_map, Rational.ChainRepresentatives.rationalSingularChainElement_map,
    ← Rational.ChainRepresentatives.rationalSingularChainElement_add]
  rfl

theorem rationalPlaneHalfOuter_sum_boundary :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneDiskBoundary.planeHalfInclusion false)).f 1 (Rational.HalfBoundaries.rationalPlaneHalfOuterChain false) +
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneDiskBoundary.planeHalfInclusion true)).f 1 (Rational.HalfBoundaries.rationalPlaneHalfOuterChain true) =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of PlaneHalf.CoordinatePlane)).d 2 1 rationalPlaneDiskFilling := by
  unfold Rational.HalfBoundaries.rationalPlaneHalfOuterChain rationalPlaneDiskFilling
  rw [Rational.ChainRepresentatives.rationalSingularChainElement_map, Rational.ChainRepresentatives.rationalSingularChainElement_map,
    ← Rational.ChainRepresentatives.rationalSingularChainElement_add, PlaneDiskBoundary.planeHalfOuterChain_sum_ambient,
    Rational.ChainRepresentatives.rationalSingularChainElement_d, PlaneDiskBoundary.planeDiskFilling_boundary]

end

/-! The full punctured product boundary is exactly the boundary of the
original singular cross product of the disk and tangent filling. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (m q : ℕ)
variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).X (q + 2))
variable (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
  (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin m))))).X (q + 1))

def fullPlaneProductBoundaryChain :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))))).X (q + 3) :=
  ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (halfToFullPuncturedProductMap m false)).f (q + 3)
      (HalfProductChain.halfProductPuncturedChain m false q B z) +
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (halfToFullPuncturedProductMap m true)).f (q + 3)
      (HalfProductChain.halfProductPuncturedChain m true q B z)

theorem halfToFullProductChain_inclusion (b : Bool) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 3)
      (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (halfToFullPuncturedProductMap m b)).f (q + 3)
        (HalfProductChain.halfProductPuncturedChain m b q B z)) =
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        1 (q + 2) (q + 3) (by omega)
        (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneDiskBoundary.planeHalfInclusion b)).f 1 (Rational.HalfBoundaries.rationalPlaneHalfOuterChain b)) B +
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        2 (q + 1) (q + 3) (by omega)
        (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PlaneDiskBoundary.planeHalfInclusion b)).f 2 (Rational.HalfBoundaries.rationalPlaneHalfFilling b))
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) := by
  have hc := congrArg (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (halfToFullProduct_inclusion m b)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hc
  have h := ConcreteCategory.congr_hom (congrArg (fun f => f.f (q + 3)) hc)
    (HalfProductChain.halfProductPuncturedChain m b q B z)
  change _ = ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (halfToFullProductMap m b)).f (q + 3)
    (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfSet.halfProductPunctureInclusion m b)).f (q + 3)
      (HalfProductChain.halfProductPuncturedChain m b q B z)) at h
  rw [HalfProductChain.halfProductPuncturedChain_inclusion, map_add] at h
  refine h.trans ?_
  have hL := Singular.CrossBoundary.singularCrossChain_naturality ℚ (PlaneDiskBoundary.planeHalfInclusion b)
    (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin m)))) 1 (q + 2) (q + 3) (by omega)
    (Rational.HalfBoundaries.rationalPlaneHalfOuterChain b) B
  have hR := Singular.CrossBoundary.singularCrossChain_naturality ℚ (PlaneDiskBoundary.planeHalfInclusion b)
    (𝟙 (TopCat.of (EuclideanSpace ℝ (Fin m)))) 2 (q + 1) (q + 3) (by omega)
    (Rational.HalfBoundaries.rationalPlaneHalfFilling b)
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z)
  rw [CategoryTheory.Functor.map_id] at hL hR
  exact congrArg₂ (fun x y => x + y) hL hR

theorem fullPlaneProductBoundaryChain_inclusion :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 3)
      (fullPlaneProductBoundaryChain m q B z) =
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        1 (q + 2) (q + 3) (by omega)
        ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of PlaneHalf.CoordinatePlane)).d 2 1 rationalPlaneDiskFilling) B +
      Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
        2 (q + 1) (q + 3) (by omega) rationalPlaneDiskFilling
        ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) := by
  rw [fullPlaneProductBoundaryChain, map_add, halfToFullProductChain_inclusion,
    halfToFullProductChain_inclusion]
  rw [← rationalPlaneHalfOuter_sum_boundary, ← rationalPlaneHalfFilling_sum,
    Singular.CrossBoundary.singularCrossChain_add_left, Singular.CrossBoundary.singularCrossChain_add_left]
  abel

theorem fullPlaneProductBoundaryChain_is_cross_boundary
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin m)))).d (q + 2) (q + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 1) z) :
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m))) ({0}ᶜ)).f (q + 3)
      (fullPlaneProductBoundaryChain m q B z) =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin m)))).d
        (q + 4) (q + 3)
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane) (TopCat.of (EuclideanSpace ℝ (Fin m)))
          2 (q + 2) (q + 4) (by omega) rationalPlaneDiskFilling B) := by
  rw [fullPlaneProductBoundaryChain_inclusion]
  erw [Singular.CrossBoundary.singularCrossChain_boundary_disk_at ℚ (TopCat.of PlaneHalf.CoordinatePlane)
    (TopCat.of (EuclideanSpace ℝ (Fin m))) (q + 1) (q + 4) (q + 3) (by omega) (by omega)]
  erw [hB]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductTo
