import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardPullback
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperModification

/-! # Picard Modification Descent -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardModificationDescent.Construction

noncomputable section

/-! Proper modifications of a normal integral scheme detect Openness Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem picardPullback_injective_of_proper_modification
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) [Nonempty U] [IsIso (f ∣_ U)] : Function.Injective (PicardPullback.Construction.picardPullback f) :=
  PicardPullback.Construction.picardPullback_injective_of_app f (AlgebraicGeometry.Quotients.FiniteDescent.ProperModification.Construction.ProperModificationFunctions.isIso_app hY f U)

theorem picardPullback_injective_of_smooth_modification
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsProper f] (p : Y ⟶ Spec (.of K)) [Smooth p]
    (U : Y.Opens) [Nonempty U] [IsIso (f ∣_ U)] : Function.Injective (PicardPullback.Construction.picardPullback f) :=
  PicardPullback.Construction.picardPullback_injective_of_app f (AlgebraicGeometry.Quotients.FiniteDescent.ProperModification.Construction.ProperModificationFunctions.smooth_isIso_app f U p)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PicardModificationDescent.Construction
