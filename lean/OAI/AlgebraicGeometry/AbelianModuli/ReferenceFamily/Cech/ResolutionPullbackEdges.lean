import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.SectionComparisonPullback
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.VerticalPullbackSquare

/-! # Resolution Pullback Edges -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ResolutionPullbackEdges

noncomputable section

/-! The constructed resolution pullback commutes with both actual
Čech augmentations, including the original coefficient morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeOneBoundary

variable {X Y : TopCat.{0}} (f : X ⟶ Y) {I : Type} (U : I → Opens Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)

def nativeCechResolutionTotalPullback :
    (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex U (injectiveResolution F).cocomplex).total (.up ℕ) ⟶
      (SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (fun i => (Opens.map f).obj (U i)) (injectiveResolution G).cocomplex).total (.up ℕ) :=
  Comparison.Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap f U
    (Abelian.ResolutionImage.abelianResolutionDirectImageMap f a (injectiveResolution F) (injectiveResolution G))

theorem nativeCechResolutionPullback_vertical :
    DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge U ((injectiveResolution F).ι.f 0) (injectiveResolution F).ι_f_zero_comp_complex_d ≫
        nativeCechResolutionTotalPullback f U a =
      Comparison.Betti.Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap f U F G a.hom ≫
        DivisorClass.Chern.FlasqueCechD.abelianCechVerticalEdge (fun i => (Opens.map f).obj (U i)) ((injectiveResolution G).ι.f 0)
          (injectiveResolution G).ι_f_zero_comp_complex_d := by
  exact VerticalPullbackSquare.cechVerticalPullbackSquare f U
    (Abelian.ResolutionImage.abelianResolutionDirectImageMap f a (injectiveResolution F) (injectiveResolution G)) a
    ((injectiveResolution F).ι.f 0) (injectiveResolution F).ι_f_zero_comp_complex_d
    ((injectiveResolution G).ι.f 0) (injectiveResolution G).ι_f_zero_comp_complex_d
    (Abelian.ResolutionImage.abelianResolutionDirectImageMap_zero f a (injectiveResolution F) (injectiveResolution G))

theorem nativeCechResolutionPullback_horizontal
    (hU : iSup U = ⊤) (hV : (⨆ i, (Opens.map f).obj (U i)) = ⊤) :
    Comparison.Betti.Cech.TopTotalAugmentation.topCechTotalAugmentation U (injectiveResolution F).cocomplex ≫ nativeCechResolutionTotalPullback f U a =
      Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a (injectiveResolution F) (injectiveResolution G) ≫
        Comparison.Betti.Cech.TopTotalAugmentation.topCechTotalAugmentation (fun i => (Opens.map f).obj (U i)) (injectiveResolution G).cocomplex :=
  Comparison.Betti.Sheaf.CechPullbackTotal.sheafCechPullbackTotalMap_topAugmentation f U
    (Abelian.ResolutionImage.abelianResolutionDirectImageMap f a (injectiveResolution F) (injectiveResolution G)) hU hV

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ResolutionPullbackEdges
