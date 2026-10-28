import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPointClass

/-! # Chow Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBaseChange.Cycles

noncomputable section

/-! # LineBundleCycles: actual affine-space bundle Chow pullback commutes with open restriction and closed pushforward -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineBundleSquareStructureMap_eq {E X E' U : Scheme.{0}}
    (p : E ⟶ X) (q : E' ⟶ U) (i : U ⟶ X) (j : E' ⟶ E)
    (h : IsPullback q j i p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    j ≫ (p ≫ f) = q ≫ (i ≫ f) := by
  rw [← Category.assoc, ← h.w, Category.assoc]

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U]
    (p : E ⟶ X) (q : E' ⟶ U) [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) (hs : IsPullback q j i p)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) (hq : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank q r)

theorem affineBundleChowExtension_openRestriction [IsOpenImmersion i] [IsOpenImmersion j]
    (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ f d) :
    DimensionChow.BundleCycles.dimensionChowTransport (affineBundleSquareStructureMap_eq p q i j hs f) (d + r)
      (Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + r) (ChowExtension.Cycles.affineBundleChowExtension p f r hp d a)) =
      ChowExtension.Cycles.affineBundleChowExtension q (i ≫ f) r hq d (Open.ChowRestriction.BundleCycles.openChowRestriction i f d a) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z]
  simp only [ChowPointClass.Cycles.affineBundleChowExtension_pointClass, Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass,
    Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle]
  rw [Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_openRestriction p q i j hs]

theorem affineBundleChowExtension_closedPushforward [IsClosedImmersion i] [IsClosedImmersion j]
    (d : ℕ) (a : DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d) :
    ChowExtension.Cycles.affineBundleChowExtension p f r hp d (Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d a) =
      Closed.ChowOver.BundleCycles.closedChowPushforwardOver j (q ≫ (i ≫ f)) (p ≫ f)
        (affineBundleSquareStructureMap_eq p q i j hs f) (d + r)
        (ChowExtension.Cycles.affineBundleChowExtension q (i ≫ f) r hq d a) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (i ≫ f) d a
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (i ≫ f) d z]
  simp only [Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass, ChowPointClass.Cycles.affineBundleChowExtension_pointClass,
    Closed.ChowPointClass.BundleCycles.closedChowPushforwardOver_pointClass]
  rw [Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality p q i j hs]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBaseChange.Cycles
