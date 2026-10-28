import OAI.AlgebraicGeometry.Divisors.LineBundles.ClopenFiberCyclePullback
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.IntegralPrincipalRelations
import OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.FiberReduced
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.PointChowAllGrades
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass

/-! # Clopen Principal Relations -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.ClopenPrincipalRelations.BundleCycles

noncomputable section

/-! The full fiber-cycle pullback preserves principal relations when the
smooth source splits into finitely many integral-fiber clopen pieces. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem smoothClopenFiberCycle_principal_zero {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [QuasiCompact p] (f : E ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    {ι : Type} [Fintype ι] (U : ι → Scheme.{0}) (i : ∀ k, U k ⟶ E)
    [∀ k, IsOpenImmersion (i k)] [∀ k, IsClosedImmersion (i k)]
    [∀ k, GeometricallyIntegral (i k ≫ p)]
    (hcover : ∀ x : E, ∃! k, x ∈ Set.range (i k))
    (d : ℕ) (W : IrreducibleCloseds X) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (FiberFundamentalCycle.BundleCycles.fiberPointCyclePullback p (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g)) = 0 := by
  let : ∀ y, IsReduced (p.fiber y) := FiberReduced.BundleCycles.smoothFiber_isReduced p
  let : ∀ k, AlgebraicGeometry.IsNoetherian (U k) := fun k => Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (i k)
  rw [ClopenFiberCyclePullback.BundleCycles.clopenFiberCyclePullback_apply p U i hcover, map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [← Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass (i k) f d,
    IntegralPrincipalRelations.BundleCycles.smoothIntegralCycleExtension_principal (i k ≫ p) W g hg,
    Principal.PointChowAllGrades.BundleCycles.pointCycleToChowQ_principal_all_grades (i k ≫ f) d, map_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.ClopenPrincipalRelations.BundleCycles
