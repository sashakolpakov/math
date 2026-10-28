import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowPower

/-! # Chow Degree Congr -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeCongr.BundleCycles

noncomputable section

/-! The genuine Chern-degree operation is unchanged when an
actual projection is replaced by an equal scheme morphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSourceChowDegree_congr {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated]
    (p q : E ⟶ X) [IsProper p] [IsProper q] [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q] (he : p = q)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d r
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α)) =
    Proper.ChowNe.BundleCycles.properChowPushforward q f d (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (q ≫ f) d r
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q f r hq d α)) := by
  subst q
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeCongr.BundleCycles
