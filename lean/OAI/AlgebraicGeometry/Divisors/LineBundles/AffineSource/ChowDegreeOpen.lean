import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ChowNe
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOpenPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowOpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection

/-! # Chow Degree Open -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeOpen.BundleCycles

noncomputable section

/-! The actual intersection degree of a proper bundle projection
commutes with restriction to an open subset of the base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X E' U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian U] [E.IsSeparated] [X.IsSeparated]
    [E'.IsSeparated] [U.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ U) [IsProper p] [IsProper q]
    [Smooth p] [Smooth q] [GeometricallyIntegral p] [GeometricallyIntegral q]
    (i : U ⟶ X) (j : E' ⟶ E) [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : q ≫ i = j ≫ p) (hc : Set.range j = p ⁻¹' Set.range i)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)

include hs hc in
theorem affineSourceChowDegree_openSquare (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d
      (Proper.ChowNe.BundleCycles.properChowPushforward p f d (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α))) =
      Proper.ChowNe.BundleCycles.properChowPushforward q (i ≫ f) d
        (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (L.pullback j) (q ≫ (i ≫ f)) d r
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q (i ≫ f) r hq d (Open.ChowRestriction.BundleCycles.openChowRestriction i f d α))) := by
  rw [Proper.ChowNe.BundleCycles.properChowPushforward_openSquare p q i j hs hc,
    LineBundle.ChowOpenPower.Cycles.separatedLineBundleChowPower_open,
    LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_transport,
    ChowOpenSquare.BundleCycles.affineSpaceSourceChowExtension_openSquare p q i j hs f r hp hq]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeOpen.BundleCycles
