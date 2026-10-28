import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GenerationStep
import OAI.AlgebraicGeometry.Divisors.LineBundles.ProjectiveChow.GeneratorsIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CartierBaseChangeIdeal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealRestrictionBaseChange
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.CompactificationNoetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineSpace.SourceBase
import OAI.AlgebraicGeometry.Divisors.LineBundles.CartesianComplementRange

/-! # Generation Base Change Step -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationBaseChangeStep.BundleCycles

noncomputable section

/-! The actual Cartier-hyperplane generation step persists after
arbitrary base change, using the pulled-back original ideal bundle. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E D X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian Y] [Y.IsSeparated]
    (p : E ⟶ X) (q : D ⟶ X) [IsProper p] [IsProper q] [Smooth p] [Smooth q]
    [GeometricallyIntegral p] [GeometricallyIntegral q]
    (s : D ⟶ E) [IsClosedImmersion s] (hs : s ≫ p = q)
    (hreg : Cartier.IdealBundle.Cycles.HasRegularPrincipalImageIdeals s) (b : Y ⟶ X)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (r : ℕ) (hp : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p (r + 1)) (hq : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank q r)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle D) (e : ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback s).sheaf ≅ L.sheaf)
    (ι : Type) [Finite ι] (hr : Nat.card ι = r + 1)
    (j : AffineSpace ι X ⟶ E) [IsOpenImmersion j] (hj : j ≫ p = (AffineSpace ι X ↘ X))
    (hcomp : Set.range s = (Set.range j)ᶜ)
    (hgen : ∀ d (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd q b ≫ f) d),
      α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd q b) f r (hq.baseChange b) (L.pullback (pullback.fst q b)) d)

include hs e hr hj hcomp hgen in
theorem projectiveChowGeneration_baseChange_step (d : ℕ) (α : DimensionChow.BundleCycles.DimensionChowQ (pullback.snd p b ≫ f) d) :
    α ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (pullback.snd p b) f (r + 1) (hp.baseChange b)
      ((Cartier.IdealBundle.Cycles.cartierIdealLineBundle s hreg).pullback (pullback.fst p b)) d := by
  let t := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap p q s hs b
  let a := LineBundles.AffineSpace.SourceBase.BundleCycles.affineSpaceRelativeBaseChangeMap p ι j hj b
  have ht := Relative.CartierBaseChangeIdeal.BundleCycles.relativeCartierBaseChangeMap_regular p q s hs b hreg
  have hqeq : t ≫ pullback.snd p b = pullback.snd q b := Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_snd p q s hs b
  let : Smooth (t ≫ pullback.snd p b) := hqeq.symm ▸ inferInstanceAs (Smooth (pullback.snd q b))
  let : GeometricallyIntegral (t ≫ pullback.snd p b) :=
    hqeq.symm ▸ inferInstanceAs (GeometricallyIntegral (pullback.snd q b))
  have hqt : LineBundles.AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank (t ≫ pullback.snd p b) r := hqeq.symm ▸ hq.baseChange b
  have hgt (m : ℕ) (β : DimensionChow.BundleCycles.DimensionChowQ ((t ≫ pullback.snd p b) ≫ f) m) :
      β ∈ ProjectiveChow.Filtration.BundleCycles.projectiveChowGenerated (t ≫ pullback.snd p b) f r hqt (L.pullback (pullback.fst q b)) m := by
    exact (ProjectiveChow.GeneratorsIso.BundleCycles.projectiveChowGenerated_projection_congr (t ≫ pullback.snd p b) f r hqt
      (pullback.snd q b) hqeq (hq.baseChange b) (L.pullback (pullback.fst q b)) m β).mp (hgen m _)
  have ha : Set.range t = (Set.range a)ᶜ := CartesianComplementRange.BundleCycles.cartesianComplement_range (pullback.fst p b) j s a t
    (AffineSpace.map ι b) (pullback.fst q b) (LineBundles.AffineSpace.SourceBase.BundleCycles.affineSpaceRelativeBaseChangeMap_isPullback p ι j hj b)
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p q s hs b) hcomp
  let e' := Cartier.IdealRestrictionBaseChange.BundleCycles.cartierIdealRestrictionBaseChangeIso s t (pullback.fst p b) (pullback.fst q b)
    (Relative.BaseChangeMap.BundleCycles.relativeBaseChangeMap_isPullback p q s hs b) hreg ht L e
  rw [ProjectiveChow.GeneratorsIso.BundleCycles.projectiveChowGenerated_lineBundleIso (pullback.snd p b) f (r + 1) (hp.baseChange b)
    (Relative.CartierBaseChangeIdeal.BundleCycles.relativeCartierBaseChangeMap_idealIso p q s hs b hreg)]
  exact ProjectiveChow.GenerationStep.BundleCycles.projectiveChowGeneration_cartier_step (pullback.snd p b) t ht f r (hp.baseChange b) hqt
    (L.pullback (pullback.fst q b)) e' ι hr a (LineBundles.AffineSpace.SourceBase.BundleCycles.affineSpaceRelativeBaseChangeMap_snd p ι j hj b) ha hgt d α

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.GenerationBaseChangeStep.BundleCycles
