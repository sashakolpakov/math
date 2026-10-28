import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.CoefficientPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ExactFunctorExtCocycle

/-! # Pullback Resolution Cocycle -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.PullbackResolutionCocycle

noncomputable section

/-! Native additive sheaf cohomology pullback carries an original
injective-resolution cocycle to its explicitly constructed inverse-image
cocycle, with the constant-sheaf normalization retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

local instance resolutionCocycle_enoughInjectives (X : TopCat.{0}) :
    EnoughInjectives (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives X
local instance resolutionCocycle_hasExt (X : TopCat.{0}) :
    HasExt.{0} (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) := hasExt_of_enoughInjectives _

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y} {G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X}
    (a : F ⟶ (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)

def abelianResolutionPulledCocycle {n : ℕ} (z : CoefficientPullback.additiveConstantZ Y ⟶ I.cocomplex.X n) :
    CoefficientPullback.additiveConstantZ X ⟶ J.cocomplex.X n :=
  ((ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))).inv ≫
    (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f).map z ≫ (CoefficientPullback.abelianCoefficientResolutionPullback f a I J).f n

theorem abelianResolutionPulledCocycle_closed {n : ℕ}
    (z : CoefficientPullback.additiveConstantZ Y ⟶ I.cocomplex.X n)
    (hz : z ≫ I.cocomplex.d n (n + 1) = 0) :
    abelianResolutionPulledCocycle f a I J z ≫ J.cocomplex.d n (n + 1) = 0 := by
  let e := (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))
  let p := (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f).map z ≫ (CoefficientPullback.abelianCoefficientResolutionPullback f a I J).f n
  have hp : p ≫ J.cocomplex.d n (n + 1) = 0 :=
    Comparison.Betti.ExtExactFunctorNaturality.resolutionMapCocycle_closed (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f) I J
      (CoefficientPullback.abelianCoefficientResolutionPullback f a I J) z hz
  exact (Category.assoc e.inv p (J.cocomplex.d n (n + 1))).trans
    ((congrArg (e.inv ≫ ·) hp).trans (comp_zero))

theorem abelianCoefficientCohomologyPullback_extMk {n : ℕ}
    (z : CoefficientPullback.additiveConstantZ Y ⟶ I.cocomplex.X n)
    (hz : z ≫ I.cocomplex.d n (n + 1) = 0) :
    CoefficientPullback.abelianCoefficientCohomologyPullback f a n (I.extMk z (n + 1) rfl hz) =
      J.extMk (abelianResolutionPulledCocycle f a I J z) (n + 1) rfl
        (abelianResolutionPulledCocycle_closed f a I J z hz) := by
  let := HasDerivedCategory.standard (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y)
  let := HasDerivedCategory.standard (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X)
  let adj := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f
  let e := (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))
  let p := CoefficientPullback.abelianCoefficientResolutionPullback f a I J
  have he := ExactFunctorExtCocycle.smallExt_mapExactFunctor_extMk (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f) I J p
    ((adj.homEquiv F G).symm a) (CoefficientPullback.abelianCoefficientResolutionPullback_zero f a I J) z hz
  change (Ext.mk₀ e.inv).comp
      (ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction.adjunctionExtMap adj (CoefficientPullback.additiveConstantZ Y) G n
        ((I.extMk z (n + 1) rfl hz).comp (Ext.mk₀ a) (add_zero n))) (zero_add n) = _
  rw [AdjunctionExtCoefficient.adjunctionExtMap_coefficient, he]
  exact J.mk₀_comp_extMk ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f).map z ≫ p.f n) (n + 1) rfl
    (Comparison.Betti.ExtExactFunctorNaturality.resolutionMapCocycle_closed (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullback f) I J p z hz) e.inv

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Abelian.PullbackResolutionCocycle
