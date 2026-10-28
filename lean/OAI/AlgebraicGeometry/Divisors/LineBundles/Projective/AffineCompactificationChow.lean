import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentInjective
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentClosed
import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowLocalization
import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChowTransportLaws
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowOpenSquare

/-! # Affine Compactification Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.AffineCompactificationChow.BundleCycles

noncomputable section

section

/-! Actual projective coefficient detection and Chow localization
prove injectivity of fiber extension on the affine complement. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian D] [AlgebraicGeometry.IsNoetherian U]
    [E.IsSeparated] [X.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (j : U ⟶ E) [IsOpenImmersion j] (hc : Set.range s = (Set.range j)ᶜ)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (HP : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (HD : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts (s ≫ p) (L.pullback s))
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)

include hc HP HD hq in
theorem projectiveCompactificationChow_openRestriction_injective (d : ℕ) :
    Function.Injective ((Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + (r + 1))).comp
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d)) := by
  have hzero (α : DimensionChow.BundleCycles.DimensionChowQ f d)
      (hα : Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + (r + 1)) (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d α) = 0) :
      α = 0 := by
    obtain ⟨β, hβ⟩ := (ChowLocalization.BundleCycles.openChowRestriction_eq_zero_iff j s hc (p ≫ f) (d + (r + 1)) _).mp hα
    let γ := DimensionChow.BundleCycles.dimensionChowTransport (Category.assoc s p f).symm (d + (r + 1)) β
    have hγ : Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm (d + (r + 1)) γ =
        AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d α := by
      change Closed.ChowOver.BundleCycles.closedChowPushforwardOver s _ _ _ _ (DimensionChow.BundleCycles.dimensionChowTransport _ _ β) = _
      rw [DimensionChowTransportLaws.BundleCycles.closedChowPushforwardOver_transport]
      exact hβ
    have hz : γ = 0 := by
      apply ProjectiveChow.MomentInjective.BundleCycles.projectiveChowMoments_joint_zero (s ≫ p) f (L.pullback s) HD r hq (d + (r + 1)) γ
      intro a n h hn
      have H := ProjectiveChow.MomentClosed.BundleCycles.projectiveChowMoment_closedPushforward p s f L (d + (r + 1)) a n h γ
      rw [hγ] at H
      exact H.symm.trans (ProjectiveChow.MomentClosed.BundleCycles.affineSpaceSourceChowMoment_pullback_zero p f L (r + 1) hp d a n h (by omega) α)
    apply Free.InfinityChartsChowDegree.BundleCycles.affineSpaceSourceChowExtension_injective_of_freeInfinityCharts p L HP f (r + 1) hp d
    rw [map_zero, ← hγ, hz, map_zero]
  intro α β h
  apply sub_eq_zero.mp
  apply hzero (α - β)
  change Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + (r + 1)) (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d α) =
    Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + (r + 1)) (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d β) at h
  rw [map_sub, map_sub, h, sub_self]

end

/-! An affine open with its actual projective compactification
inherits injectivity of genuine Chow fiber extension in positive rank. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian D] [AlgebraicGeometry.IsNoetherian U]
    [E.IsSeparated] [X.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (j : U ⟶ E) [IsOpenImmersion j] (hc : Set.range s = (Set.range j)ᶜ)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (HP : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (HD : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts (s ≫ p) (L.pullback s))
    (q : U ⟶ X) [Smooth q] [GeometricallyIntegral q] (hj : j ≫ p = q)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hD : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q (r + 1))

include hc HP HD hj hp hD in
theorem affineProjectiveCompactificationChowExtension_injective (d : ℕ) :
    Function.Injective (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q f (r + 1) hq d) := by
  intro α β hαβ
  apply projectiveCompactificationChow_openRestriction_injective p s j hc L HP HD f r hp hD d
  change Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + (r + 1)) (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d α) =
    Open.ChowRestriction.BundleCycles.openChowRestriction j (p ≫ f) (d + (r + 1)) (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d β)
  apply DimensionChowTransportLaws.BundleCycles.dimensionChowTransport_injective
    (show j ≫ (p ≫ f) = q ≫ f by rw [← Category.assoc, hj]) (d + (r + 1))
  rw [AffineSource.ChowOpenSquare.BundleCycles.affineSpaceSourceChowExtension_openOver p q j hj f (r + 1) hp hq,
    AffineSource.ChowOpenSquare.BundleCycles.affineSpaceSourceChowExtension_openOver p q j hj f (r + 1) hp hq]
  exact hαβ

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.AffineCompactificationChow.BundleCycles
