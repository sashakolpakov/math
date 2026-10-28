import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.PullbackResolutionCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResolutionImage
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdditiveConstantPullbackNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.CechPullbackTotal

/-! # Resolution Section Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResolutionSectionCoordinates

noncomputable section

/-! The native pulled-back Ext cocycle is the ordinary global-section
pullback of the original resolution cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)

def abelianResolutionSectionsPullback :
    Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex I.cocomplex ⟶
      Comparison.Betti.Cech.TopTotalAugmentation.additiveTopGlobalComplex J.cocomplex :=
  Comparison.Betti.Sheaf.CechPullbackTotal.topGlobalSectionsPullback f (ResolutionImage.abelianResolutionDirectImageMap f a I J)

theorem abelianResolutionSectionsPullback_coordinate {n : ℕ}
    (z : CoefficientPullback.additiveConstantZ Y ⟶ I.cocomplex.X n) :
    (abelianResolutionSectionsPullback f a I J).f n (AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (I.cocomplex.X n) z) =
      AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (J.cocomplex.X n) (PullbackResolutionCocycle.abelianResolutionPulledCocycle f a I J z) := by
  let adj := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f
  let b := (ResolutionImage.abelianResolutionDirectImageMap f a I J).f n
  have h := AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv_coefficientPullback f b z
  have hb : (adj.homEquiv _ _).symm b = (CoefficientPullback.abelianCoefficientResolutionPullback f a I J).f n :=
    (adj.homEquiv _ _).symm_apply_apply _
  rw [hb] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResolutionSectionCoordinates
