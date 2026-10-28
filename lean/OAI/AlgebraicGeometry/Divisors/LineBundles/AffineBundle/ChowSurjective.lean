import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowBelowRank

/-! # Chow Surjective -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowSurjective.Cycles

noncomputable section

/-! # LineBundleCycles: genuine global surjectivity of constant-rank affine-space bundle Chow pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineBundleChowExtension_surjective {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ) (h : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank p r) (d : ℕ) :
    Function.Surjective (ChowExtension.Cycles.affineBundleChowExtension p f r h d) := by
  apply ChowBelowRank.Cycles.affineBundleSurjectiveOnClosed_all f r ⊤ X (𝟙 X) _ f (Category.id_comp f) E p h d
  ext x
  simp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.ChowSurjective.Cycles
