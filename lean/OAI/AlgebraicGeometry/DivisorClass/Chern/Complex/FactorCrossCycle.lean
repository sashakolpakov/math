import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ProductFactorMaps
import OAI.AlgebraicGeometry.DivisorClass.Chern.Relative.CrossFilling

/-! # Factor Cross Cycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.FactorCrossCycle

noncomputable section

/-! The actual relative product cycle in the original complex factors,
with its exact ambient cross-product representative. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem relativeCycleMap_projection {X Y : TopCat.{0}} (f : X ⟶ Y)
    {A : Set X} {B : Set Y} (h : Set.MapsTo f A B) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ X A) n)
    (b : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).X n)
    (hz : z.val = (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ X A).f n b) :
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h) n z).val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ Y B).f n (((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f).f n b) := by
  change (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ f h).f n z.val = _
  rw [hz]
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => g.f n) (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection_naturality ℚ f h)) b

def complexFactorCrossCycle (p : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ)))
      ({0}ᶜ)) (2 * p + 4) :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (ProductFactorMaps.complexProductFactorMap p) (ProductFactorMaps.complexProductFactorMap_puncture p))
    (2 * p + 4)
    (PlaneProductCycle.fullPlaneProductRelativeCycle (2 * p + 2) (2 * p) (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p))
      (DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p)).val (DiskProductSphereGenerator.euclideanOrthantRationalFilling_boundary (2 * p)))

theorem complexFactorCrossCycle_val (p : ℕ) :
    (complexFactorCrossCycle p).val =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ)).f (2 * p + 4)
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (Fin 1 → ℂ)) (TopCat.of (Fin (p + 1) → ℂ))
          2 (2 * p + 2) (2 * p + 4) (by omega)
          Rational.DiskGenerator.normalSupportedDiskRationalFilling (Rational.PositiveComplexSphere.positiveComplexRationalFilling p)) := by
  unfold complexFactorCrossCycle
  rw [relativeCycleMap_projection (ProductFactorMaps.complexProductFactorMap p) (ProductFactorMaps.complexProductFactorMap_puncture p)
    (2 * p + 4) _ (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of PlaneHalf.CoordinatePlane)
      (TopCat.of (EuclideanSpace ℝ (Fin (2 * p + 2)))) 2 (2 * p + 2) (2 * p + 4) (by omega)
      PlaneProductTo.rationalPlaneDiskFilling (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p))) rfl]
  have hn := Singular.CrossBoundary.singularCrossChain_naturality ℚ DiskGenerator.planeToNormalLine (Positive.ComplexCoordinates.positiveEuclideanToComplex p)
    2 (2 * p + 2) (2 * p + 4) (by omega) PlaneProductTo.rationalPlaneDiskFilling (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p))
  rw [ProductFactorMaps.normalSupportedDiskRationalFilling_of_plane, ProductFactorMaps.positiveComplexRationalFilling_of_euclidean] at hn
  exact congrArg ((CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainProjection ℚ
    (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ)).f (2 * p + 4)) hn

theorem complexFactorCrossCycle_line_class (p : ℕ) :
    homologyMap (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (ProductFactorMaps.complexProductLineMap p) (ProductFactorMaps.complexProductLineMap_puncture p))
      (2 * p + 4) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ
        (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ)) (2 * p + 4)
        (complexFactorCrossCycle p)) = DiskProductGenerator.complexDiskProductFillingClass p := by
  have hc := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality
    (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainsMap ℚ (ProductFactorMaps.complexProductFactorMap p) (ProductFactorMaps.complexProductFactorMap_puncture p))
    (2 * p + 4)
    (PlaneProductCycle.fullPlaneProductRelativeCycle (2 * p + 2) (2 * p) (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p))
      (DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p)).val (DiskProductSphereGenerator.euclideanOrthantRationalFilling_boundary (2 * p)))
  change _ = AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ
    (TopCat.of ((Fin 1 → ℂ) × (Fin (p + 1) → ℂ))) ({0}ᶜ)) (2 * p + 4) (complexFactorCrossCycle p) at hc
  rw [← hc]
  have hm := CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarHomologyMap_comp ℚ (ProductFactorMaps.complexProductFactorMap p) (ProductFactorMaps.complexProductLineMap p)
    (ProductFactorMaps.complexProductFactorMap_puncture p) (ProductFactorMaps.complexProductLineMap_puncture p) (2 * p + 4)
  exact ConcreteCategory.congr_hom hm
    (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ
      (TopCat.of (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2)))) ({0}ᶜ)) (2 * p + 4)
      (PlaneProductCycle.fullPlaneProductRelativeCycle (2 * p + 2) (2 * p) (DiskProductSphereGenerator.euclideanOrthantRationalFilling (2 * p))
        (DiskProductSphereGenerator.euclideanOrthantRationalPuncturedCycle (2 * p)).val (DiskProductSphereGenerator.euclideanOrthantRationalFilling_boundary (2 * p))))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.FactorCrossCycle
