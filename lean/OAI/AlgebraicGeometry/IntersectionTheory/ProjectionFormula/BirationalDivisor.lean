import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalLocalSection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardFiber
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.StalkIso

/-! # Birational Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalDivisor

noncomputable section

/-! Proper birational pushforward preserves principal-divisor coefficients
over valuation-ring points, using the unique actual fiber and its stalk
isomorphism. In particular this applies at divisor points of a normal target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

universe u

theorem principalDivisor_coefficient {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    [IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη)] (y : Y)
    [ValuationRing (Y.presheaf.stalk y)] (g : Y.functionField) :
    CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g)) y =
      (Y.ord g y : ℚ) := by
  obtain ⟨x, hx, huniq⟩ := BirationalLocalSection.proper_valuationFiber_unique f hη y
  let : ValuationRing (Y.presheaf.stalk (f x)) := by rw [hx]; infer_instance
  let := BirationalStalk.stalkMap_isIso_of_valuation f hη x
  rw [PushforwardFiber.pointPushforward_uniqueFiber f x y hx huniq,
    BirationalStalk.residueDegree_of_valuation f hη x, Nat.cast_one, mul_one,
    Affine.DivisorNorm.rationalPrincipalDivisor_apply]
  have h := Divisor.StalkIso.ord_eq_of_stalkMap_isIso f hη x
    (BirationalStalk.coheight_of_valuation f hη x) g
  rw [hx] at h
  exact congrArg (fun n : ℤ => (n : ℚ)) h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalDivisor
