import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiberRelation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ClosedFiberClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.ZeroEquation

/-! # Supported Cartier Fiber Relation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SupportedCartierFiberRelation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: principal Cartier fiber intersection kills every support relation
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Z]

theorem schemePrincipalPointDivisor_eq_pointPushforward (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g = IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g) := by
  rw [IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion]
  exact Finsupp.embDomain_eq_mapDomain _ _

theorem principalCartier_fiber_principal_zero (j : Z ⟶ X) [IsClosedImmersion j]
    (a : Γ(X, ⊤)) (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (W : IrreducibleCloseds X) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 2)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d
      (Principal.CartierFiber.BundleCycles.principalCartierPointMap a (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g)) = 0 := by
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι W
  let k := pullback.fst i j
  let q := pullback.snd i j
  let : AlgebraicGeometry.IsNoetherian (pullback i j) := Finite.Fiber.BundleCycles.finiteMorphism_noetherian q
  have hs : Point.CycleChow.BundleCycles.closedPointCycleToChowQ k (i ≫ f) d
      (Principal.CartierFiber.BundleCycles.principalCartierPointMap (i.appTop a) (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g)) = 0 := by
    by_cases ha : i.appTop a = 0
    · rw [ha, Cartier.ZeroEquation.BundleCycles.principalCartierPointMap_zero_equation, map_zero]
    · exact Principal.CartierFiberRelation.BundleCycles.principalCartier_fiber_class_zero k (i.appTop a) (Finite.Fiber.BundleCycles.pullbackClosed_zeroFiber i j a hzero)
        (i ≫ f) ha d hW (Units.mk0 g hg)
  have hc := Finite.ClosedFiberClass.BundleCycles.finiteClosedFiber_class_zero i j f d _ hs
  rw [Finite.CartierPushforward.BundleCycles.finitePushforward_principalCartierPointMap i f a,
    ← schemePrincipalPointDivisor_eq_pointPushforward W g] at hc
  exact hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SupportedCartierFiberRelation.BundleCycles
