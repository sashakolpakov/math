import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.PrincipalPushforward
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

/-! # Isomorphism Divisor Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.IsomorphismDivisorPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: residue-weighted pushforward of principal divisors under isomorphism
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem pointPushforward_eq_mapDomain_of_immersion {X Y : Scheme}
    (f : X ⟶ Y) [IsPreimmersion f] (z : X →₀ ℚ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f z = Finsupp.mapDomain f z := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, Finsupp.mapDomain_add, hz, hw]
  | single x a =>
    rw [IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single, IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle.residueDegree_immersion,
      Nat.cast_one, mul_one, Finsupp.mapDomain_single]

theorem isomorphismPrincipalDivisor_pushforward {X Y : Scheme}
    [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsIso f] (hη : f (genericPoint X) = genericPoint Y)
    (g : Y.functionField) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g)) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y g := by
  have he : (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso f).inv (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g) = g :=
    Iso.hom_inv_id_apply (RationalDivisorRestriction.BundleCycles.openFunctionFieldIso f) g
  exact (pointPushforward_eq_mapDomain_of_immersion f _).trans
    ((Closed.PrincipalPushforward.BundleCycles.rationalPrincipalDivisor_iso (asIso f) _).trans
      (congrArg (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y) he))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.IsomorphismDivisorPushforward.BundleCycles
