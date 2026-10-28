import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.CartierFiberRelation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CartierPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.Fiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward

/-! # Cartier Fiber Relation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiberRelation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: principal Cartier intersection kills rational divisors on singular supports

The finite normalization proves the normal case. Its actual pulled-back
zero fiber maps finitely to the original fiber; the Cartier projection
formula and complete divisor pushforward descend the vanishing.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Z : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Z]

theorem principalCartier_fiber_class_zero (j : Z ⟶ X) [IsClosedImmersion j]
    (a : Γ(X, ⊤)) (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (ha : a ≠ 0) (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2) (g : X.functionFieldˣ) :
    Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d
      (CartierFiber.BundleCycles.principalCartierPointMap a (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (g : X.functionField))) = 0 := by
  let ν := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X
  let : IsFinite ν := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X f
  let : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  let k := pullback.fst ν j
  let q := pullback.snd ν j
  let : AlgebraicGeometry.IsNoetherian (pullback ν j) := Finite.Fiber.BundleCycles.finiteMorphism_noetherian q
  have hn := Normal.CartierFiberRelation.BundleCycles.normalPrincipalCartier_fiber_class_zero k (ν.appTop a)
    (Finite.Fiber.BundleCycles.pullbackClosed_zeroFiber ν j a hzero) (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X) (ν ≫ f)
    (Finite.Fiber.BundleCycles.genericPullback_globalSection_ne_zero ν (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationMap_genericPoint X) a ha) d
    ((NormalizationResidue.BundleCycles.finiteNormalization_dimension X f).trans hX) (NormalizationResidue.BundleCycles.normalizationFunctionUnit X g)
  let c : IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X →₀ ℚ := CartierFiber.BundleCycles.principalCartierPointMap (ν.appTop a)
    (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom (g : X.functionField)))
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (k ≫ ν ≫ f) d
    (Finsupp.comapDomain k c k.isClosedEmbedding.injective.injOn) = 0 at hn
  have hmap : k ≫ ν ≫ f = q ≫ j ≫ f := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  rw [hmap] at hn
  have hc := congrArg (Finite.ChowPushforward.BundleCycles.finiteChowPushforward q (j ≫ f) d) hn
  rw [map_zero, Finite.ChowPointClass.BundleCycles.finiteChowPushforward_pointClass] at hc
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (j ≫ f) d
    (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (pullback.snd ν j)
      (Finsupp.comapDomain (pullback.fst ν j) c (pullback.fst ν j).isClosedEmbedding.injective.injOn)) = 0 at hc
  rw [Closed.FiberPushforward.BundleCycles.pullbackClosed_pointPushforward] at hc
  change Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward ν c) = 0 at hc
  change Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d
    (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward ν (CartierFiber.BundleCycles.principalCartierPointMap (ν.appTop a)
      (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom (g : X.functionField))))) = 0 at hc
  rw [Finite.CartierPushforward.BundleCycles.finitePushforward_principalCartierPointMap ν f a,
    NormalizationDivisorPushforward.BundleCycles.normalizationPrincipalDivisor_pushforward X f (g : X.functionField) g.ne_zero] at hc
  exact hc

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiberRelation.BundleCycles
