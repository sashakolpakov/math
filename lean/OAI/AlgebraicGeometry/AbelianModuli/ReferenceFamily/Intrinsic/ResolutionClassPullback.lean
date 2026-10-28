import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.ResolutionSectionCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCohomologyMap

/-! # Resolution Class Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ResolutionClassPullback

noncomputable section

/-! Pullback of the native sheaf class of an actual resolution section
is the class of its original direct-image section pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCohomologyMap

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)

theorem abelianResolutionSectionsPullback_closed {n : ℕ}
    (s : (I.cocomplex.X n).obj.obj (op ⊤))
    (hs : (I.cocomplex.d n (n + 1)).hom.app (op ⊤) s = 0) :
    (J.cocomplex.d n (n + 1)).hom.app (op ⊤)
      ((Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a I J).f n s) = 0 := by
  let p := Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a I J
  have h := ConcreteCategory.congr_hom (p.comm n (n + 1)) s
  change (J.cocomplex.d n (n + 1)).hom.app (op ⊤) (p.f n s) =
    p.f (n + 1) ((I.cocomplex.d n (n + 1)).hom.app (op ⊤) s) at h
  exact h.trans ((congrArg (p.f (n + 1)) hs).trans (map_zero (p.f (n + 1)).hom))

theorem nativeResolutionClass_pullback {n : ℕ}
    (s : (I.cocomplex.X n).obj.obj (op ⊤))
    (hs : (I.cocomplex.d n (n + 1)).hom.app (op ⊤) s = 0) :
    Abelian.CoefficientPullback.abelianCoefficientCohomologyPullback f a n (DivisorClass.Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass I n s hs) =
      DivisorClass.Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass J n ((Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a I J).f n s)
        (abelianResolutionSectionsPullback_closed f a I J s hs) := by
  let z := (AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (I.cocomplex.X n)).symm s
  have hz : z ≫ I.cocomplex.d n (n + 1) = 0 := by
    apply (AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (I.cocomplex.X (n + 1))).injective
    rw [AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv_natural, AddEquiv.apply_symm_apply, map_zero]
    exact hs
  have hc := Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback_coordinate f a I J z
  have he : Abelian.PullbackResolutionCocycle.abelianResolutionPulledCocycle f a I J z =
      (AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (J.cocomplex.X n)).symm
        ((Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a I J).f n s) := by
    apply (AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (J.cocomplex.X n)).injective
    exact (hc.symm.trans (congrArg ((Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a I J).f n)
      ((AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (I.cocomplex.X n)).apply_symm_apply s))).trans
        ((AdditiveConstantPullbackNormalization.additiveHomTopSectionsEquiv (J.cocomplex.X n)).apply_symm_apply
          ((Abelian.ResolutionSectionCoordinates.abelianResolutionSectionsPullback f a I J).f n s)).symm
  have h := Abelian.PullbackResolutionCocycle.abelianCoefficientCohomologyPullback_extMk f a I J z hz
  refine h.trans ?_
  unfold DivisorClass.Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass
  congr 1

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ResolutionClassPullback
