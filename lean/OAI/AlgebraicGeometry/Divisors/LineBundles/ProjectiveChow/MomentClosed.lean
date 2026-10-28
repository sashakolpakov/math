import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration
import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowPowerComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowPowerVanishing
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChartsChowDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection

/-! # Moment Closed -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentClosed.BundleCycles

noncomputable section

section

/-! Proper pushforwards of actual intersection powers form the
triangular coefficient tests for projective Chow generators. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [E.IsSeparated] [X.IsSeparated] (p : E ⟶ X) [IsProper p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)

def projectiveChowMoment (d s n : ℕ) (h : d = s + n) :
    DimensionChow.BundleCycles.DimensionChowQ (p ≫ f) d →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f s :=
  (Proper.ChowNe.BundleCycles.properChowPushforward p f s).comp ((LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) s n).comp
    (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h).toLinearMap)

variable [Smooth p] [GeometricallyIntegral p] (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

theorem projectiveChowMoment_component (d s n k i : ℕ) (h : d = s + n) (hd : k + r = d + i)
    (β : DimensionChow.BundleCycles.DimensionChowQ f k) :
    projectiveChowMoment p f L d s n h (Filtration.BundleCycles.projectiveChowComponent p f r hp L d k i hd β) =
      Proper.ChowNe.BundleCycles.properChowPushforward p f s (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) s (n + i)
        (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl (show k + r = s + (n + i) by omega)
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp k β))) := by
  subst d
  change Proper.ChowNe.BundleCycles.properChowPushforward p f s (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) s n
    (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) (s + n) i
      (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp k β)))) = _
  rw [ChowPowerComposition.BundleCycles.separatedLineBundleChowPower_add, ChowPowerComposition.BundleCycles.dimensionChowReindexEquiv_trans]

theorem projectiveChowMoment_component_zero (d s n k i : ℕ) (h : d = s + n) (hd : k + r = d + i)
    (hks : k < s) (β : DimensionChow.BundleCycles.DimensionChowQ f k) :
    projectiveChowMoment p f L d s n h (Filtration.BundleCycles.projectiveChowComponent p f r hp L d k i hd β) = 0 := by
  rw [projectiveChowMoment_component p f L r hp]
  exact AffineSource.ChowPowerVanishing.BundleCycles.affineSpaceSourceChowExtension_power_pushforward_zero p f r hp L k s (n + i) hks (by omega) β

theorem projectiveChowMoment_component_top (H : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (d s n i : ℕ) (h : d = s + n) (hd : s + r = d + i) (hi : n + i = r)
    (β : DimensionChow.BundleCycles.DimensionChowQ f s) :
    projectiveChowMoment p f L d s n h (Filtration.BundleCycles.projectiveChowComponent p f r hp L d s i hd β) = (-1 : ℚ) ^ r • β := by
  subst r
  rw [projectiveChowMoment_component p f L (n + i) hp]
  exact Free.InfinityChartsChowDegree.BundleCycles.freeInfinityCharts_chow_degree p L H f (n + i) hp s β

end

/-! The actual proper intersection tests commute with a closed
hyperplane image, and the lower tests kill a bundle fiber extension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian D] [E.IsSeparated] [X.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [IsProper p] (s : D ⟶ E) [IsClosedImmersion s]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)

theorem projectiveChowMoment_closedPushforward (d a n : ℕ) (h : d = a + n)
    (α : DimensionChow.BundleCycles.DimensionChowQ ((s ≫ p) ≫ f) d) :
    projectiveChowMoment p f L d a n h
      (Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm d α) =
      projectiveChowMoment (s ≫ p) f (L.pullback s) d a n h α := by
  change Proper.ChowNe.BundleCycles.properChowPushforward p f a (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) a n
    (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl h
      (Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm d α))) = _
  rw [ChowPowerComposition.BundleCycles.closedChowPushforwardOver_reindex, ← LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed s,
    ← LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_properOver_projection s, LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed s,
    LineBundle.ChowOverProjection.Cycles.properChowPushforward_closedOver_comp p s f]
  rfl

theorem affineSpaceSourceChowMoment_pullback_zero {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [X.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (d a n : ℕ) (h : d + r = a + n)
    (hn : n < r) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    projectiveChowMoment p f L (d + r) a n h (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α) = 0 :=
  projectiveChowMoment_component_zero p f L r hp (d + r) a n d 0 h rfl (by omega) α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.MomentClosed.BundleCycles
