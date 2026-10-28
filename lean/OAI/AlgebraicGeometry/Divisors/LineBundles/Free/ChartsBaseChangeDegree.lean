import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveInfinityChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RelativeBaseChangeChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveDegreeBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.BasisSourceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.RankCommonOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSource.ChowDegreeOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.TopDimensionChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineBundle.Localization

/-! # Charts Base Change Degree -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsBaseChangeDegree.BundleCycles

noncomputable section

/-! Actual finite free infinity charts determine the top degree
after an arbitrary integral base change, including singular supports. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated] [IsIntegral Y]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (b : Y ⟶ X) (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r)

include H in
theorem freeInfinityCharts_baseChange_top_degree (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d)
    (α : DimensionChow.BundleCycles.DimensionChowQ f d) :
    Proper.ChowNe.BundleCycles.properChowPushforward (pullback.snd p b) f d
      (LineBundle.SeparatedChowPower.Cycles.separatedLineBundleChowPower (L.pullback (pullback.fst p b)) (pullback.snd p b ≫ f) d r
        (AffineSpace.SourceChowExtension.BundleCycles.affineSpaceSourceChowExtension (pullback.snd p b) f r (hp.baseChange b) d α)) =
      (-1 : ℚ) ^ r • α := by
  obtain ⟨C⟩ := H (b (genericPoint Y))
  let R := C.coefficient
  let M := C.module
  let : Module.Finite R M := Module.Finite.of_basis C.basis
  let q := SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)
  have hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q C.rank := by
    simpa only [Nat.card_fin] using Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts C.basis
  let : Smooth q := hq.forget.smooth
  let : GeometricallyIntegral q := Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_geometricallyIntegral C.basis
  let U := pullback b C.baseMap
  let k : U ⟶ Y := pullback.fst b C.baseMap
  let c : U ⟶ Spec R := pullback.snd b C.baseMap
  let : IsOpenImmersion k := inferInstanceAs (IsOpenImmersion (pullback.fst b C.baseMap))
  let : AlgebraicGeometry.IsNoetherian U := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian k
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from k]; infer_instance⟩
  obtain ⟨a, ha⟩ := C.contains
  obtain ⟨u, hu, hau⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback b C.baseMap)
    (genericPoint Y) a ha.symm
  let : Nonempty U := ⟨u⟩
  let : IsIntegral U := isIntegral_of_isOpenImmersion k
  let t := Open.RelativeBaseChangeChart.BundleCycles.openRelativeBaseChangeChartMap p q C.baseMap C.totalMap C.square b
  have hs : IsPullback (pullback.snd q c) t k (pullback.snd p b) :=
    Open.RelativeBaseChangeChart.BundleCycles.openRelativeBaseChangeChart_projection_isPullback p q C.baseMap C.totalMap C.square b
  have hcard : r = C.rank := AffineSource.RankCommonOpen.BundleCycles.affineSpaceSourceRank_openSquare (pullback.snd p b) (pullback.snd q c)
    k t hs.w f r C.rank (hp.baseChange b) (hq.baseChange c) u
  subst r
  let e := LineBundle.PullbackIso.Cycles.lineBundlePullbackSquareIso L (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle R M)
    (pullback.fst p b) C.totalMap t (pullback.fst q c)
    (Open.RelativeBaseChangeChart.BundleCycles.openRelativeBaseChangeChartMap_fst p q C.baseMap C.totalMap C.square b) C.idealIso
  apply TopDimensionChow.BundleCycles.openChowRestriction_top_injective f k d hd
  rw [AffineSource.ChowDegreeOpen.BundleCycles.affineSourceChowDegree_openSquare (pullback.snd p b) (pullback.snd q c) k t hs.w
      (AffineBundle.Localization.Cycles.schemePullback_range (pullback.snd p b) (pullback.snd q c) k t hs) f
      (L.pullback (pullback.fst p b)) C.rank (hp.baseChange b) (hq.baseChange c),
    LineBundle.SeparatedChowIso.Cycles.separatedLineBundleChowPower_iso e,
    ProjectiveDegreeBaseChange.BundleCycles.freeProjectiveChow_baseChange_degree C.basis c (k ≫ f) C.rank (Nat.card_fin C.rank) hq,
    map_smul]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsBaseChangeDegree.BundleCycles
