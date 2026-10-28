import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.TopDimensionChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityDegreeAllRanks
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.Localization

/-! # Projective Chart Top Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveChartTopDegree.BundleCycles

noncomputable section

/-! An actual finite free projective chart around the generic point
determines the top intersection degree over an integral base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [X.IsSeparated] [IsIntegral X]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    {R M ι : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Fintype ι]
    (b : Module.Basis ι R M)
    [Smooth (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    [GeometricallyIntegral (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M))]
    (i : Spec (.of R) ⟶ X) (j : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) ⟶ E)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) j i p)
    (e : (L.pullback j).sheaf ≅ (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M).sheaf)
    (n : ℕ) (hn : Nat.card ι = n)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p n)
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) n)

include b hs e hn hq in
theorem freeProjectiveChart_top_degree (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d)
    (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d n
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f n hp d α)) = (-1 : ℚ) ^ n • α := by
  apply TopDimensionChow.BundleCycles.openChowRestriction_top_injective f i d hd
  rw [AffineSource.ChowDegreeOpen.BundleCycles.affineSourceChowDegree_openSquare p (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) i j hs.w
    (AffineBundle.Localization.Cycles.schemePullback_range p (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) i j hs) f L n hp hq,
    LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso e,
    InfinityDegreeAllRanks.BundleCycles.freeSymmetricInfinityChow_degree b (i ≫ f) n hn hq, map_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveChartTopDegree.BundleCycles
