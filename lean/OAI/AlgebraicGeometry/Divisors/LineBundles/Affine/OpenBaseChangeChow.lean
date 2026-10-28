import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.ProjectiveCompactificationChowEquiv
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsOpenBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsRankFromOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.CartesianComplementRange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian

/-! # Open Base Change Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenBaseChangeChow.BundleCycles

noncomputable section

/-! The actual compactification criterion applies on an open base
using infinity charts of the restricted divisor alone. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X D A U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian D]
    [X.IsSeparated] [D.IsSeparated]
    (p : E ⟶ X) [IsProper p] [Smooth p] [GeometricallyIntegral p]
    (q : A ⟶ X) [Smooth q] [GeometricallyIntegral q] (t : D ⟶ X)
    (s : D ⟶ E) [IsClosedImmersion s] (hs : s ≫ p = t)
    (j : A ⟶ E) [IsOpenImmersion j] (hj : j ≫ p = q)
    (hc : Set.range s = (Set.range j)ᶜ)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (HP : Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L)
    (i : U ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (r : ℕ)
    (HD : Free.InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank (pullback.snd t i)
      ((L.pullback s).pullback (pullback.fst t i)) r)
    (hq : AffineSpace.BundleRankZero.Cycles.HasAffineSpaceChartsOfRank (pullback.snd q i) (r + 1))

include hs hj hc HP HD in
theorem affineCompactification_openBaseChange_Chow_bijective
    [AlgebraicGeometry.IsNoetherian U] [AlgebraicGeometry.IsNoetherian (pullback q i : Scheme)] (d : ℕ) :
    Function.Bijective (AffineBundle.ChowExtension.Cycles.affineBundleChowExtension (pullback.snd q i) (i ≫ f) (r + 1) hq d) := by
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from i]; infer_instance⟩
  let : AlgebraicGeometry.IsNoetherian (pullback t i : Scheme) := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (pullback.fst t i)
  let : (pullback t i : Scheme).IsSeparated := ⟨by rw [← terminal.comp_from (pullback.fst t i)]; infer_instance⟩
  let s' := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p t s hs i
  let j' := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p q j hj i
  have hS := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p t s hs i
  have hJ := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p q j hj i
  let : IsOpenImmersion j' := MorphismProperty.of_isPullback hJ.flip inferInstance
  have hs' : s' ≫ pullback.snd p i = pullback.snd t i := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd p t s hs i
  have hj' : j' ≫ pullback.snd p i = pullback.snd q i := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd p q j hj i
  have HP' := Free.ChartsOpenBaseChange.BundleCycles.freeInfinityCharts_openBaseChange p L i HP
  have hP := (Free.ChartsRankFromOpen.BundleCycles.freeInfinityCharts_rank_of_open (pullback.snd p i) (pullback.snd q i) j' hj'
    (L.pullback (pullback.fst p i)) HP' (i ≫ f) (r + 1) hq.sourceCharts).sourceCharts
  let e := LineBundle.PullbackIso.Cycles.lineBundlePullbackSquareIso L (L.pullback s) (pullback.fst p i) s s' (pullback.fst t i)
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_fst p t s hs i) (Iso.refl _)
  have HD' : Free.InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank (s' ≫ pullback.snd p i)
      ((L.pullback (pullback.fst p i)).pullback s') r := by
    rw [hs']
    exact HD.changeLineBundle _ e
  let : Smooth (s' ≫ pullback.snd p i) := Free.InfinityCharts.BundleCycles.freeInfinityCharts_smooth _ _ HD'.forget
  let : GeometricallyIntegral (s' ≫ pullback.snd p i) := Free.InfinityCharts.BundleCycles.freeInfinityCharts_geometricallyIntegral _ _ HD'.forget
  have hc' : Set.range s' = (Set.range j')ᶜ :=
    CartesianComplementRange.BundleCycles.cartesianComplement_range (pullback.fst p i) j s j' s' (pullback.fst q i) (pullback.fst t i) hJ hS hc
  exact ProjectiveCompactificationChowEquiv.BundleCycles.affineProjectiveCompactificationChow_bijective (pullback.snd p i) s' j' hc'
    (L.pullback (pullback.fst p i)) HP' HD'.forget (pullback.snd q i) hj'
    (i ≫ f) r hP HD'.sourceCharts hq d

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenBaseChangeChow.BundleCycles
