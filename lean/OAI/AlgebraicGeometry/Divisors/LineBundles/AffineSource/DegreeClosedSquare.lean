import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowClosedSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowClosedSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection

/-! # Degree Closed Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.DegreeClosedSquare.BundleCycles

noncomputable section

/-! The genuine intersection-degree operation commutes with
pushforward from any closed base and its actual inverse image. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U] [E.IsSeparated] [X.IsSeparated] [E'.IsSeparated] [U.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ U) [IsProper p] [IsProper q] [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsClosedImmersion i] [IsClosedImmersion j]
    (hs : IsPullback q j i p) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (r : ℕ)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)

include hs in
theorem affineSourceChowDegree_closedSquare (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (i ≫ f) d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d (Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d α))) =
      Closed.ChowPushforward.BundleCycles.closedChowPushforward i f d
        (Proper.ChowNe.BundleCycles.properChowPushforward q (i ≫ f) d
          (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (L.pullback j) (q ≫ (i ≫ f)) d r
            (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q (i ≫ f) r hq d α))) := by
  rw [ChowClosedSquare.BundleCycles.affineSpaceSourceChowExtension_closedPushforward p q i j hs f r hp hq,
    ← LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed j,
    ← LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_properOver_projection j,
    LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed j,
    Proper.ChowClosedSquare.BundleCycles.properChowPushforward_closedSquare p q i j hs f]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.DegreeClosedSquare.BundleCycles
