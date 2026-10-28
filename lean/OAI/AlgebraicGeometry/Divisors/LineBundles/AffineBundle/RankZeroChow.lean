import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.BundleRankZero
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SourceChowComparison
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsomorphismInverse

/-! # Rank Zero Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.RankZeroChow.Cycles

noncomputable section

/-! The actual Chow fiber extension of any zero-rank affine-space
bundle is bijective in every dimension grade. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p 0)

theorem affineBundleChowExtension_rankZero_bijective (d : ℕ) :
    Function.Bijective (ChowExtension.Cycles.affineBundleChowExtension p f 0 h d) := by
  let : IsIso p := AffineSpace.BundleRankZero.Cycles.affineBundleRankZero_isIso p h
  rw [SourceChowComparison.Cycles.affineBundleChowExtension_eq_sourceCharts p f 0 h h.sourceCharts]
  constructor
  · exact Function.LeftInverse.injective (AffineSource.ChowIsomorphismDegree.BundleCycles.affineSpaceSourceChowExtension_isomorphism_degree p f h.sourceCharts d)
  · intro α
    exact ⟨Proper.ChowNe.BundleCycles.properChowPushforward p f d α,
      AffineSource.ChowIsomorphismInverse.BundleCycles.affineSpaceSourceChowExtension_isomorphism_rightInverse p f h.sourceCharts d α⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.RankZeroChow.Cycles
