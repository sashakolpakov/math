import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.Filtration
import OAI.AlgebraicGeometry.Divisors.LineBundles.ChowPowerComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso

/-! # Hyperplane Generators -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.HyperplaneGenerators.BundleCycles

noncomputable section

/-! Pushforward from an actual relative Cartier hyperplane shifts
the constructed projective Chow generators by one intersection. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian D] [E.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (hreg : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback s).sheaf ≅ L.sheaf)

include e in
theorem projectiveChowComponent_hyperplane (d k i : ℕ) (hd : k + r = d + i)
    (β : DimensionChow.BundleCycles.DimensionChowQ f k) :
    Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm d
      (Filtration.BundleCycles.projectiveChowComponent (s ≫ p) f r hq L d k i hd β) =
      -Filtration.BundleCycles.projectiveChowComponent p f (r + 1) hp (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg) d k (i + 1)
        (by omega) β := by
  have hc : Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm (k + r)
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq k β) =
      -LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg) (p ≫ f) (k + r)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp k β) := by
    rw [Relative.CartierFiberChow.BundleCycles.relativeCartierIdeal_fiber_chow p s hreg f r hp hq, neg_neg]
  change Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm d
    (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L ((s ≫ p) ≫ f) d i
      (DimensionChowReindex.BundleCycles.dimensionChowReindexEquiv rfl hd (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq k β))) = _
  rw [← LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso e,
    ← LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed s,
    LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_properOver_projection s,
    LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed s,
    ← ChowPowerComposition.BundleCycles.closedChowPushforwardOver_reindex s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm
      (k + r) (d + i) hd,
    hc, map_neg, map_neg, ChowPowerComposition.BundleCycles.separatedLineBundleChowIntersection_reindex]
  rfl

include e in
theorem projectiveChowGenerated_hyperplane (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ ((s ≫ p) ≫ f) d)
    (hα : α ∈ Filtration.BundleCycles.projectiveChowGenerated (s ≫ p) f r hq L d) :
    Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm d α ∈
      Filtration.BundleCycles.projectiveChowGenerated p f (r + 1) hp (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg) d := by
  induction hα using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, i, hi, hd, β, rfl⟩ := ha
    rw [projectiveChowComponent_hyperplane p s hreg f r hp hq L e]
    exact Submodule.neg_mem _ (Filtration.BundleCycles.projectiveChowComponent_mem_generated p f (r + 1) hp
      (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg) d k (i + 1) (by omega) (by omega) β)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b ha hb ia ib => rw [map_add]; exact Submodule.add_mem _ ia ib
  | smul c a ha ia => rw [map_smul]; exact Submodule.smul_mem _ c ia

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.HyperplaneGenerators.BundleCycles
