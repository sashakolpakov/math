import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ResolutionClassPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveCochainClassRepresentatives

/-! # Section Comparison Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionComparisonPullback

noncomputable section

/-! The native comparison between resolution-section homology and
sheaf Ext cohomology commutes with actual pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

def nativeTopResolutionCohomologyMap {X : TopCat.{0}} (F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) (n : ℕ) :
    (Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex (injectiveResolution F).cocomplex).homology (n + 1) ⟶
      (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) (n + 1)).obj F :=
  DivisorClass.Chern.Intrinsic.SectionCohomologyMap.nativeInjectiveSectionCohomologyMap F n

theorem nativeTopResolutionCohomologyMap_class {X : TopCat.{0}} (F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) (n : ℕ)
    (s : ((injectiveResolution F).cocomplex.X (n + 1)).obj.obj (op ⊤))
    (hs : ((injectiveResolution F).cocomplex.d (n + 1) (n + 2)).hom.app (op ⊤) s = 0) :
    nativeTopResolutionCohomologyMap F n
      ((Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex (injectiveResolution F).cocomplex).homologyπ (n + 1)
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ s hs)) = DivisorClass.Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (injectiveResolution F) (n + 1) s hs :=
  DivisorClass.Chern.Intrinsic.SectionCohomologyMap.nativeInjectiveSectionCohomologyMap_class F n s hs

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)

theorem nativeTopResolutionCohomologyMap_pullback (n : ℕ)
    (x : (Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex (injectiveResolution F).cocomplex).homology (n + 1)) :
    Abelian.CoefficientPullback.abelianCoefficientCohomologyPullback f a (n + 1) (nativeTopResolutionCohomologyMap F n x) =
      nativeTopResolutionCohomologyMap G n
        (HomologicalComplex.homologyMap
          (Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a (injectiveResolution F) (injectiveResolution G)) (n + 1) x) := by
  let I := injectiveResolution F
  let J := injectiveResolution G
  let K := Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex I.cocomplex
  let p := Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a I J
  obtain ⟨s, hs, rfl⟩ := PositiveCochainClassRepresentatives.positiveCochainClass_surjective K n x
  have hps := ResolutionClassPullback.abelianResolutionSectionsPullback_closed f a I J s hs
  have hm := SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n p s hs hps
  have hF := nativeTopResolutionCohomologyMap_class F n s hs
  have hG := nativeTopResolutionCohomologyMap_class G n (p.f (n + 1) s) hps
  exact (congrArg (Abelian.CoefficientPullback.abelianCoefficientCohomologyPullback f a (n + 1)) hF).trans
    ((ResolutionClassPullback.nativeResolutionClass_pullback f a I J s hs).trans
      (hG.symm.trans (congrArg (nativeTopResolutionCohomologyMap G n) hm).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionComparisonPullback
