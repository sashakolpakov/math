import OAI.AlgebraicGeometry.CycleClass.Thom.Smooth
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection

/-! # Smooth Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SmoothIntersection.Constructions

noncomputable section

/-! The independently defined geometric classes multiply for smooth
supports whose actual intersection is smooth and transverse. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Smooth.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions
  Intersection.Constructions.ThomAbsolute Cycle.Degree.Constructions.Class Supported.Intersection.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
  [Smooth A.structureMap] [Smooth B.structureMap] [Smooth C.structureMap]

theorem geometricCycleClass_intersection
    (hC : (C.val : Set V.carrier) = (A.val : Set V.carrier) ∩ (B.val : Set V.carrier))
    (ht : Immersion.IntersectionCoordinates.Constructions.NormalTransverse (SmoothImmersion.Constructions.smoothCycleImmersion A) (SmoothImmersion.Constructions.smoothCycleImmersion B)) :
    C.geometricCycleClass =
      cast (congrArg (fun n => (V.rationalCohomology n : Type)) (add_add_add_comm p p q q))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) (p + p) (q + q)
          A.geometricCycleClass B.geometricCycleClass) := by
  have hw : Set.range C.regularAnalyticToAmbient =
      Set.range A.regularAnalyticToAmbient ∩ Set.range B.regularAnalyticToAmbient := by
    rw [SmoothImmersion.Constructions.regular_range_eq_support, SmoothImmersion.Constructions.regular_range_eq_support, SmoothImmersion.Constructions.regular_range_eq_support,
      C.range_analyticInclusion, A.range_analyticInclusion, B.range_analyticInclusion,
      hC, Set.preimage_inter]
  have h := Intersection.Constructions.ThomAbsolute.regularThomClass_absolute_intersection
    (SmoothImmersion.Constructions.smoothCycleImmersion A) (SmoothImmersion.Constructions.smoothCycleImmersion B) (SmoothImmersion.Constructions.smoothCycleImmersion C) hw ht
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
    (Set.range C.regularAnalyticToAmbient)ᶜ (2 * (p + q)) (SmoothImmersion.Constructions.smoothCycleImmersion C).regularThomClass =
    eqToHom (congrArg (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace))
      (Nat.mul_add 2 p q).symm)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (TopCat.of V.analyticSpace) (2 * p) (2 * q)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
          (Set.range A.regularAnalyticToAmbient)ᶜ (2 * p) (SmoothImmersion.Constructions.smoothCycleImmersion A).regularThomClass)
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
          (Set.range B.regularAnalyticToAmbient)ᶜ (2 * q) (SmoothImmersion.Constructions.smoothCycleImmersion B).regularThomClass)) at h
  rw [Thom.Smooth.Constructions.smoothThom_absoluteClass C, Thom.Smooth.Constructions.smoothThom_absoluteClass A, Thom.Smooth.Constructions.smoothThom_absoluteClass B] at h
  have hc := congrArg (cast (congrArg (fun n => (V.rationalCohomology n : Type))
    (two_mul (p + q)))) h
  rw [← Cycle.Degree.Constructions.Class.rationalCycleClass_as_cast, GeometricTrace.Constructions.HigherThom.rationalCycleClass_eq_geometric] at hc
  have hab := Supported.Intersection.Constructions.Class.supportedIntersectionClass_geometricCup A B
  rw [Supported.Intersection.Constructions.Class.supportedIntersectionClass_forget] at hab
  exact hc.trans hab

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SmoothIntersection.Constructions
