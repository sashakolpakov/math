import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChangeIdeal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealRestrictionBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierFiberChowPower
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeCongr
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian

/-! # Cartier Degree Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierDegreeBaseChange.BundleCycles

noncomputable section

/-! The relative Cartier top-degree reduction remains valid after
every base change, with the actual pulled-back ideal line bundles. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E D X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : E ⟶ X) (q : D ⟶ X) [IsProper p] [IsProper q] [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (s : D ⟶ E) [IsClosedImmersion s] (hs : s ≫ p = q)
    (hreg : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) (b : Y ⟶ X)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1))
    (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback s).sheaf ≅ L.sheaf)

include hs e in
theorem relativeCartierDegree_baseChange (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd p b) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback (pullback.fst p b))
        (pullback.snd p b ≫ f) d (r + 1)
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd p b) f (r + 1) (hp.baseChange b) d α)) =
      -Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd q b) f d
        (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (L.pullback (pullback.fst q b)) (pullback.snd q b ≫ f) d r
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd q b) f r (hq.baseChange b) d α)) := by
  let t := BaseChangeMap.BundleCycles.relativeBaseChangeMap p q s hs b
  have ht := CartierBaseChangeIdeal.BundleCycles.relativeCartierBaseChangeMap_regular p q s hs b hreg
  have hcomp : t ≫ pullback.snd p b = pullback.snd q b := BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd p q s hs b
  let : Smooth (t ≫ pullback.snd p b) := hcomp.symm ▸ inferInstanceAs (Smooth (pullback.snd q b))
  let : GeometricallyIntegral (t ≫ pullback.snd p b) :=
    hcomp.symm ▸ inferInstanceAs (GeometricallyIntegral (pullback.snd q b))
  have hqt : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (t ≫ pullback.snd p b) r := hcomp.symm ▸ hq.baseChange b
  let e' := Cartier.IdealRestrictionBaseChange.BundleCycles.cartierIdealRestrictionBaseChangeIso s t (pullback.fst p b) (pullback.fst q b)
    (BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p q s hs b) hreg ht L e
  have H := CartierFiberChowPower.BundleCycles.relativeCartierIdeal_topDegree_reduction (pullback.snd p b) t ht f r (hp.baseChange b) hqt
    (L.pullback (pullback.fst q b)) e' d α
  rw [← LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso (CartierBaseChangeIdeal.BundleCycles.relativeCartierBaseChangeMap_idealIso p q s hs b hreg)] at H
  exact H.trans (congrArg Neg.neg (AffineSource.ChowDegreeCongr.BundleCycles.affineSourceChowDegree_congr (t ≫ pullback.snd p b)
    (pullback.snd q b) hcomp f (L.pullback (pullback.fst q b)) r hqt (hq.baseChange b) d α))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierDegreeBaseChange.BundleCycles
