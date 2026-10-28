import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdjunctionExtCoefficient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactFunctorResolutionComparison
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology

/-! # Coefficient Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CoefficientPullback

noncomputable section

/-! Pullback of arbitrary additive sheaf coefficients has a constructed
resolution map normalized by the original direct-image morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian
open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction

abbrev additiveConstantZ (X : TopCat.{0}) : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X :=
  (constantSheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift ℤ))

local instance coefficientPullback_enoughInjectives (X : TopCat.{0}) :
    EnoughInjectives (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives X

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)

def abelianCoefficientCohomologyPullback (n : ℕ) :
    CategoryTheory.Sheaf.H F n →+ CategoryTheory.Sheaf.H G n :=
  (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPushforwardCohomologyMap f G n).comp (CategoryTheory.Sheaf.H.map a n)

def abelianCoefficientResolutionPullback (I : InjectiveResolution F) (J : InjectiveResolution G) :
    ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ J.cocomplex :=
  ExactFunctorResolutionComparison.exactFunctorResolutionComparison (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f) I J
    (((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f).homEquiv F G).symm a)

theorem abelianCoefficientResolutionPullback_zero
    (I : InjectiveResolution F) (J : InjectiveResolution G) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f).map (I.ι.f 0) ≫ (abelianCoefficientResolutionPullback f a I J).f 0 =
      ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f).homEquiv F G).symm a ≫ J.ι.f 0 :=
  ExactFunctorResolutionComparison.exactFunctorResolutionComparison_zero (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f) I J
    (((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f).homEquiv F G).symm a)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CoefficientPullback
