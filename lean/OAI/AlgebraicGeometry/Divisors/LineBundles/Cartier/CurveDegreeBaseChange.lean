import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChangeIdeal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.CurveChowDegree
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChowIso

/-! # Curve Degree Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.CurveDegreeBaseChange.BundleCycles

noncomputable section

/-! The degree of a relative Cartier section of a proper curve
is minus one after arbitrary base change, on every Chow class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E D X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (s : D ⟶ E) [IsClosedImmersion s] [IsIso (s ≫ p)]
    (hreg : IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) (b : Y ⟶ X)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p 1)

theorem cartierCurveChow_baseChange_degree (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd p b) f d
      (LineBundle.SeparatedChow.Cycles.separatedLineBundleChowIntersection ((IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback (pullback.fst p b))
        (pullback.snd p b ≫ f) d
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd p b) f 1 (hp.baseChange b) d α)) = -α := by
  let t := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p (s ≫ p) s rfl b
  have ht := Relative.CartierBaseChangeIdeal.BundleCycles.relativeCartierBaseChangeMap_regular p (s ≫ p) s rfl b hreg
  have hcomp : t ≫ pullback.snd p b = pullback.snd (s ≫ p) b :=
    Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd p (s ≫ p) s rfl b
  let : IsIso (t ≫ pullback.snd p b) := by rw [hcomp]; infer_instance
  rw [LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowIntersection_iso (Relative.CartierBaseChangeIdeal.BundleCycles.relativeCartierBaseChangeMap_idealIso p (s ≫ p) s rfl b hreg)]
  exact CurveChowDegree.BundleCycles.cartierCurveChow_pullback_degree (pullback.snd p b) (hp.baseChange b) t ht f d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.CurveDegreeBaseChange.BundleCycles
