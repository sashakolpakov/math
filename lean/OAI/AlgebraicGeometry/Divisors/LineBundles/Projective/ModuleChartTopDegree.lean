import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleTopDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChartsPullback

/-! # Module Chart Top Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleChartTopDegree.BundleCycles

noncomputable section

/-! A genuine finite projective module chart computes the top
intersection degree of a proper bundle over an integral base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [X.IsSeparated] [IsIntegral X]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    {R M : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (i : Spec (.of R) ⟶ X) (j : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) ⟶ E)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)) j i p)
    (e : (L.pullback j).sheaf ≅ (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M).sheaf)
    (n : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p n)

include hs e in
theorem projectiveModuleChart_top_degree (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d)
    (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d n
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f n hp d α)) = (-1 : ℚ) ^ n • α := by
  let q := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)
  have hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q n := hp.of_isPullback q i j hs
  apply TopDimensionChow.BundleCycles.openChowRestriction_top_injective f i d hd
  rw [AffineSource.ChowDegreeOpen.BundleCycles.affineSourceChowDegree_openSquare p q i j hs.w (AffineBundle.Localization.Cycles.schemePullback_range p q i j hs)
    f L n hp hq, LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso e,
    ModuleTopDegree.BundleCycles.projectiveModuleChow_top_degree R M (i ≫ f) n hq d
      ((Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i f).trans hd), map_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ModuleChartTopDegree.BundleCycles
