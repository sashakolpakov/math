import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportRegularFunction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Support.PrincipalLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber

/-! # Cartier Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CartierPushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite pushforward commutes with the actual principal Cartier cycles
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] (i : X ⟶ Y) [IsFinite i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include f

theorem finitePushforward_principalCartierPointCycle (a : Γ(Y, ⊤)) (x : X) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Principal.CartierCycle.BundleCycles.principalCartierPointCycle (i.appTop a) (irreducibleSetEquivPoints.symm x)) =
      (i.residueDegree x : ℚ) • Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm (i x)) := by
  have hs := Point.SupportRegularFunction.BundleCycles.pointSupportFunctionFieldMap_regular i x a
  by_cases hg : Principal.CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm (i x)) = 0
  · have hz : Principal.CartierCycle.BundleCycles.supportRegularFunction (i.appTop a) (irreducibleSetEquivPoints.symm x) = 0 := by
      rw [hg, map_zero] at hs
      exact hs.symm
    simp only [Principal.CartierCycle.BundleCycles.principalCartierPointCycle, hz, hg, Principal.CartierCycle.BundleCycles.schemePrincipalPointDivisor_zero, map_zero, smul_zero]
  · have hsg : Principal.CartierCycle.BundleCycles.supportRegularFunction (i.appTop a) (irreducibleSetEquivPoints.symm x) ≠ 0 := by
      rw [← hs]
      exact (map_ne_zero_iff (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap i x).hom
        (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap i x).hom.injective).mpr hg
    change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor _ _) = _
    rw [FiniteSupport.Divisor.BundleCycles.finitePushforward_principalPointSupport i f x _ hsg, Point.SupportRegularFunction.BundleCycles.finitePointSupportNorm_regular,
      Support.PrincipalLaws.BundleCycles.schemePrincipalPointDivisor_pow _ _ hg]
    rfl

theorem finitePushforward_principalCartierPointMap (a : Γ(Y, ⊤)) (z : X →₀ ℚ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (Principal.CartierFiber.BundleCycles.principalCartierPointMap (i.appTop a) z) =
      Principal.CartierFiber.BundleCycles.principalCartierPointMap a (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    rw [Principal.CartierFiber.BundleCycles.principalCartierPointMap_single, map_smul,
      finitePushforward_principalCartierPointCycle i f a x, IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single,
      Principal.CartierFiber.BundleCycles.principalCartierPointMap_single, smul_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CartierPushforward.BundleCycles
