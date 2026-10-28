import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.SupportClasses
import OAI.AlgebraicGeometry.CycleClass.Thom.BilinearSupportSum

/-! # Proper Intersection Class -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.ProperIntersectionClass.Constructions

noncomputable section

/-! Finite properly meeting rational cycles satisfy the actual
Serre/cup formula by bilinearity on their nonzero support pairs. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Proper.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.SupportClasses.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.IntersectionBettiBilinear OAI.AlgebraicGeometry.CycleClass.Thom.BilinearSupportSum.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)

theorem intersectionBilinear_class (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : IntersectionGeometry.MeetProperly X p q a b) :
    X.geometricCycleClassMap (p + q) (Intersection.intersectionBilinear X p q a b) =
      ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear X p q (X.geometricCycleClassMap p a) (X.geometricCycleClassMap q b) := by
  let F := (Intersection.intersectionBilinear X p q).compr₂ (X.geometricCycleClassMap (p + q))
  let G := (ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear X p q).compl₁₂ (X.geometricCycleClassMap p) (X.geometricCycleClassMap q)
  apply BilinearSupportSum.Constructions.bilinear_apply_eq_of_support_pairs F G a b
  intro A hA B hB
  have hp := Intersection.SupportClasses.Constructions.pair_cycle_class X p q A B (h A hA B hB)
  simpa only [F, G, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Intersection.intersectionBilinear,
    Finsupp.linearCombination_single, one_smul] using hp

theorem properIntersection_class (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) (hc : IntersectionGeometry.IsProperIntersectionCycle X p q a b c) :
    X.geometricCycleClassMap (p + q) c =
      ComponentRestriction.Constructions.IntersectionBettiBilinear.intersectionBettiBilinear X p q (X.geometricCycleClassMap p a) (X.geometricCycleClassMap q b) := by
  have he := IntersectionGeometry.isProperIntersectionCycle_unique X p q hc (Intersection.intersectionBilinear_isProper X p q a b hc.1)
  rw [he]
  exact intersectionBilinear_class X p q a b hc.1

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.ProperIntersectionClass.Constructions
