import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicIrreducibleIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.ReducedLocalIntersection

/-! # Smooth Serre Intersection -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SmoothSerreIntersection.Constructions

noncomputable section

/-! A geometric Serre-cup comparison for smooth transverse intersections
whose actual local equations give a reduced regular intersection. The
finite cycle uses exactly the original categorical Tor multiplicities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.IntersectionCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SmoothIntersection.Constructions
  IntrinsicIrreducibleIntersection.Constructions.Intrinsic Supported.Map.Constructions Supported.ProjectiveSupportIsolation.Constructions.Intersection
  SupportStalkModule.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + q))
  [Smooth A.structureMap] [Smooth B.structureMap] [Smooth C.structureMap]

theorem geometricClass_supportedSerreCycle
    (hC : (C.val : Set V.carrier) = (A.val : Set V.carrier) ∩ (B.val : Set V.carrier))
    (ht : Immersion.IntersectionCoordinates.Constructions.NormalTransverse (SmoothImmersion.Constructions.smoothCycleImmersion A) (SmoothImmersion.Constructions.smoothCycleImmersion B))
    (hxA : IntersectionGeometry.supportPoint C.val ∈ (A.val : Set V.carrier))
    (hxB : IntersectionGeometry.supportPoint C.val ∈ (B.val : Set V.carrier))
    (rs : List (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val)))
    (hA : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap V.carrier A.val (IntersectionGeometry.supportPoint C.val) hxA).hom = Ideal.ofList rs)
    (hr : IsWeaklyRegular (V.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C.val)) rs)
    (hB : IsWeaklyRegular (IntersectionGeometry.localSupportModule V.carrier B.val (IntersectionGeometry.supportPoint C.val) hxB) rs)
    (hmax : (Ideal.ofList rs).map (SupportStalkModule.Constructions.supportStalkMap V.carrier B.val (IntersectionGeometry.supportPoint C.val) hxB).hom =
      IsLocalRing.maximalIdeal ((Geometric.GenericPoint.reducedSupportScheme B.val).presheaf.stalk
        (IntersectionGeometry.supportPreimage B.val (IntersectionGeometry.supportPoint C.val) hxB))) :
    V.geometricCycleClassMap (p + q)
      (Supported.Map.Constructions.forgetCycle V (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed V p q A B) (p + q)
        (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle V p q A B (IntrinsicIrreducibleIntersection.Constructions.Intrinsic.intersection_dimension_bound A B C hC))) =
      cast (congrArg (fun n => (V.rationalCohomology n : Type)) (add_add_add_comm p p q q))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) (p + p) (q + q)
          A.geometricCycleClass B.geometricCycleClass) := by
  rw [IntrinsicIrreducibleIntersection.Constructions.Intrinsic.supportedPairCycle_forget_eq_single A B C hC,
    ReducedLocalIntersection.Constructions.intersectionMultiplicity_eq_one V.presentation
      A.val B.val C.val hxA hxB rs hA hr hB hmax,
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, one_smul]
  exact SmoothIntersection.Constructions.geometricCycleClass_intersection A B C hC ht

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SmoothSerreIntersection.Constructions
