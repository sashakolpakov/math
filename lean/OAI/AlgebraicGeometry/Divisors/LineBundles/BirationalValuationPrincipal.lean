import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationComp
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber

/-! # Birational Valuation Principal -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationPrincipal.BundleCycles.BirationalValuationDivisor

noncomputable section

/-! # LineBundleCycles: proper birational pushforward preserves actual principal-divisor coefficients over valuation rings -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem principalDivisor_coefficient {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (y : Y)
    [ValuationRing (Y.presheaf.stalk y)] (g : Y.functionField) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g)) y =
      (Y.ord g y : ℚ) := by
  obtain ⟨x, hx, huniq⟩ := BirationalValuationComp.BundleCycles.BirationalValuationSection.proper_valuationFiber_unique f hη y
  let : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  let := BirationalValuationOf.BundleCycles.BirationalValuationStalk.stalkMap_isIso_of_valuation f hη x
  rw [IntersectionTheory.ProjectionFormula.PushforwardFiber.pointPushforward_uniqueFiber f x y hx huniq,
    BirationalValuationOf.BundleCycles.BirationalValuationStalk.residueDegree_of_valuation f hη x, Nat.cast_one, mul_one,
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor_apply]
  have h := MorphismOrderStalk.BundleCycles.ord_of_stalkMap_isIso f hη x (BirationalValuationOf.BundleCycles.BirationalValuationStalk.coheight_of_valuation f hη x) g
  exact congrArg (fun n : ℤ => (n : ℚ)) (h.trans (congrArg (fun y => Y.ord g y) hx))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalValuationPrincipal.BundleCycles.BirationalValuationDivisor
