import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowPointClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceChowPointClass

/-! # Source Chow Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SourceChowComparison.Cycles

noncomputable section

/-! The Chow maps constructed from full affine-bundle charts and
from affine-space source charts agree by their actual cycle formula. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineBundleChowExtension_eq_sourceCharts
    {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) (h' : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (d : ℕ) :
    ChowExtension.Cycles.affineBundleChowExtension p f r h d = AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r h' d := by
  ext α
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f d α
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion f d z, ChowPointClass.Cycles.affineBundleChowExtension_pointClass,
    AffineSpace.SourceChowPointClass.BundleCycles.affineSpaceSourceChowExtension_pointClass]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.SourceChowComparison.Cycles
