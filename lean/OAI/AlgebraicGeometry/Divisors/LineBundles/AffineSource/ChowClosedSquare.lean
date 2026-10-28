import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBaseChange

/-! # Chow Closed Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowClosedSquare.BundleCycles

noncomputable section

/-! Actual Chow fiber extension from source charts commutes with
pushforward from a closed base and its cartesian inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U]
    (p : E ⟶ X) (q : E' ⟶ U) [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsClosedImmersion i] [IsClosedImmersion j]
    (hs : IsPullback q j i p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)

theorem affineSpaceSourceChowExtension_closedPushforward (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d) :
    AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d (Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d α) =
      Closed.ChowOver.BundleCycles.closedChowPushforwardOver j (q ≫ (i ≫ f)) (p ≫ f)
        (AffineBundle.ChowBaseChange.Cycles.affineBundleSquareStructureMap_eq p q i j hs f) (d + r)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q (i ≫ f) r hq d α) := by
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective (i ≫ f) d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion (i ≫ f) d z, Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass,
    AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass, AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass,
    Closed.ChowPointClass.BundleCycles.closedChowPushforwardOver_pointClass, Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality p q i j hs]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowClosedSquare.BundleCycles
