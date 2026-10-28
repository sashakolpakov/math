import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowIsoPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowOverProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso

/-! # Chow Degree Iso -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeIso.BundleCycles

noncomputable section

/-! The genuine Chern-degree calculation is preserved by
an actual relative scheme isomorphism and actual line-bundle isomorphism. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem affineSourceChowDegree_iso
    {E E' X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian E] [AlgebraicGeometry.IsNoetherian E']
    [AlgebraicGeometry.IsNoetherian X] [E.IsSeparated] [E'.IsSeparated] [X.IsSeparated]
    (p : E ⟶ X) (q : E' ⟶ X) [IsProper p] [IsProper q] [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (j : E' ⟶ E) [IsIso j] (hj : j ≫ p = q)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E') (e : (L.pullback j).sheaf ≅ M.sheaf)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward p f d (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower L (p ≫ f) d r
      (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension p f r hp d α)) =
      Proper.ChowNe.BundleCycles.properChowPushforward q f d (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower M (q ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q f r hq d α)) := by
  have hf : j ≫ (p ≫ f) = q ≫ f := by rw [← Category.assoc, hj]
  have hcomp (β : DimensionChow.BundleCycles.DimensionChowQ (q ≫ f) d) :
      Proper.ChowNe.BundleCycles.properChowPushforward p f d (Proper.ChowFunctoriality.BundleCycles.properChowPushforwardOver j (q ≫ f) (p ≫ f) hf d β) =
        Proper.ChowNe.BundleCycles.properChowPushforward q f d β := by
    subst q
    rw [LineBundle.ChowOverProjection.Cycles.properChowPushforwardOver_eq_closed]
    exact LineBundle.ChowOverProjection.Cycles.properChowPushforward_closedOver_comp p j f d β
  have hExt := ChowIsoPushforward.BundleCycles.affineSpaceSourceChowExtension_isoPushforward p q j hj f r hp hq d α
  have hPower := LineBundle.ChowOverProjection.Cycles.separatedLineBundleChowPower_properOver_projection j (q ≫ f) (p ≫ f) hf L d r
    (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension q f r hq d α)
  rw [← hExt, ← hPower, hcomp, LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso e (q ≫ f) d r]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeIso.BundleCycles
