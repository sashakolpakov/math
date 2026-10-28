import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation

/-! # Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Intersection

noncomputable section

/-! The diagonal cup construction is supported on the same original
closed algebraic intersection as the actual Serre intersection cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Constructions.Class

open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Intersection.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorCupForget.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)

theorem intersectionSupport_eq :
    Set.range A.analyticInclusion ∩ Set.range B.analyticInclusion =
      V.analyticUnderlying ⁻¹' (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B : Set V.carrier) := by
  rw [A.range_analyticInclusion, B.range_analyticInclusion]
  rfl

def closedIntersectionClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of V.analyticSpace)
    (V.analyticUnderlying ⁻¹' (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B : Set V.carrier))ᶜ (2 * (p + q)) :=
  eqToHom (congrArg (fun S : Set V.analyticSpace =>
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) S (2 * (p + q)))
    (congrArg Set.compl (intersectionSupport_eq V p q A B))) (Supported.Intersection.Constructions.Class.supportedIntersectionClass A B)

theorem closedIntersectionClass_geometricCup :
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (two_mul (p + q)))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
        (V.analyticUnderlying ⁻¹' (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B : Set V.carrier))ᶜ (2 * (p + q))
        (closedIntersectionClass V p q A B)) =
    cast (congrArg (fun n => (V.rationalCohomology n : Type)) (add_add_add_comm p p q q))
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) (p + p) (q + q)
        A.geometricCycleClass B.geometricCycleClass) := by
  have h := ExteriorCupForget.Constructions.relativeInclusion_supportCast (TopCat.of V.analyticSpace)
    (congrArg (fun S : Set V.analyticSpace => Sᶜ) (intersectionSupport_eq V p q A B))
    (2 * (p + q)) (Supported.Intersection.Constructions.Class.supportedIntersectionClass A B)
  exact (congrArg (cast (congrArg (fun n => (V.rationalCohomology n : Type))
    (two_mul (p + q)))) h).trans (Supported.Intersection.Constructions.Class.supportedIntersectionClass_geometricCup A B)

end Constructions.Class

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Closed.Intersection
