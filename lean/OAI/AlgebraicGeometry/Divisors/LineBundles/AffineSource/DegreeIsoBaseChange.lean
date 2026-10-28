import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.BaseChangeMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso

/-! # Degree Iso Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.DegreeIsoBaseChange.BundleCycles

noncomputable section

/-! A genuine isomorphism of relative schemes and their line
bundles preserves the intersection-degree operation after base change. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

instance relativeBaseChangeMap_isIso {E D X Y : Scheme.{0}}
    (p : E ⟶ X) (q : D ⟶ X) (j : D ⟶ E) [IsIso j] (hj : j ≫ p = q) (b : Y ⟶ X) :
    IsIso (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p q j hj b) :=
  (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p q j hj b).isIso_fst_of_isIso

variable {E D X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : E ⟶ X) (q : D ⟶ X) [IsProper p] [IsProper q] [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (j : D ⟶ E) [IsIso j] (hj : j ≫ p = q) (b : Y ⟶ X)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : (L.pullback j).sheaf ≅ M.sheaf)
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r) (hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)

include hj e in
theorem affineSourceChowDegree_iso_baseChange (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd p b) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (L.pullback (pullback.fst p b)) (pullback.snd p b ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd p b) f r (hp.baseChange b) d α)) =
      Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd q b) f d
        (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (M.pullback (pullback.fst q b)) (pullback.snd q b ≫ f) d r
          (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd q b) f r (hq.baseChange b) d α)) := by
  let k := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p q j hj b
  let e' := LineBundle.PullbackIso.Cycles.lineBundlePullbackSquareIso L M (pullback.fst p b) j k (pullback.fst q b)
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_fst p q j hj b) e
  exact ChowDegreeIso.BundleCycles.affineSourceChowDegree_iso (pullback.snd p b) (pullback.snd q b) k
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd p q j hj b) f (L.pullback (pullback.fst p b))
    (M.pullback (pullback.fst q b)) e' r (hp.baseChange b) (hq.baseChange b) d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.DegreeIsoBaseChange.BundleCycles
