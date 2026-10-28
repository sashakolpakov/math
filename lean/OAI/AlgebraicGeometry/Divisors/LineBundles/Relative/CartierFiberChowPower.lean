import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso

/-! # Cartier Fiber Chow Power -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChowPower.BundleCycles

noncomputable section

section

/-! Repeated actual Chern intersection of a pulled-back class
reduces by one intersection to the relative Cartier divisor. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian D]
    [E.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (hs : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)

theorem relativeCartierIdeal_fiber_chowPower (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) d (r + 1)
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d α) =
      -Closed.ChowOver.BundleCycles.closedChowPushforwardOver s ((s ≫ p) ≫ f) (p ≫ f) (Category.assoc s p f).symm d
        (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs).pullback s) ((s ≫ p) ≫ f) d r
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq d α)) := by
  rw [LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower_succ, CartierFiberChow.BundleCycles.relativeCartierIdeal_fiber_chow p s hs f r hp hq, map_neg]
  congr 1
  have H := LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_properOver_projection s ((s ≫ p) ≫ f) (p ≫ f)
    (Category.assoc s p f).symm (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) d r
    (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq d α)
  rw [LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed, LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed] at H
  exact H.symm

end

/-! The top Chern-degree calculation for a projective bundle
reduces to its actual relative Cartier hyperplane. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {E X D : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian D]
    [E.IsSeparated] [X.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [Smooth (s ≫ p)] [GeometricallyIntegral (s ≫ p)]
    (hs : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (s ≫ p) r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs).pullback s).sheaf ≅ L.sheaf)

include e in
theorem relativeCartierIdeal_topDegree_reduction (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hs) (p ≫ f) d (r + 1)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f (r + 1) hp d α)) =
      -Proper.ChowNe.BundleCycles.properChowPushforward (s ≫ p) f d
        (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L ((s ≫ p) ≫ f) d r
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (s ≫ p) f r hq d α)) := by
  rw [relativeCartierIdeal_fiber_chowPower p s hs f r hp hq, map_neg,
    LineBundle.ChowOverProjection.Cycles.properChowPushforward_closedOver_comp p s f d,
    LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso e ((s ≫ p) ≫ f) d r]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChowPower.BundleCycles
