import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.ProperIntersectionClass
import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDescent

/-! # Core -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Core

noncomputable section

/-! ThomClass intersection compatibility for the original geometric cycle
class, genuine Serre–Tor multiplicities, and principal-divisor equivalence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Thom.Proper.ProperIntersectionClass.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalDescent.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.IntersectionBettiBilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Cycle classes take actual algebraic intersection modulo genuine
principal-divisor rational equivalence to the original cup product. -/
theorem cycle_class_intersection
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p)
    (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q))
    (hc : IntersectionGeometry.RepresentsIntersection X p q a b c) :
    X.geometricCycleClassMap (p + q) c =
      cast
        (congrArg (fun n => (X.rationalCohomology n : Type))
          (add_add_add_comm p p q q))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ)
          (Betti.Scheme.schemePointSpace X.toOver) (p + p) (q + q)
          (X.geometricCycleClassMap p a)
          (X.geometricCycleClassMap q b)) := by
  obtain ⟨a', b', c', ha, hb, hp, hc'⟩ := hc
  rw [PrincipalDescent.Constructions.geometricClass_eq_of_rationallyEquivalent X (p + q) hc',
    PrincipalDescent.Constructions.geometricClass_eq_of_rationallyEquivalent X p ha,
    PrincipalDescent.Constructions.geometricClass_eq_of_rationallyEquivalent X q hb]
  exact (Proper.ProperIntersectionClass.Constructions.properIntersection_class X p q a' b' c' hp).trans
    (ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear_apply X p q _ _)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Core
