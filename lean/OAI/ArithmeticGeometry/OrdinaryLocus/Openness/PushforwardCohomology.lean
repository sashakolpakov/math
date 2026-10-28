import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTerminal

/-! # Pushforward Cohomology -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction

noncomputable section

/-! Comparison from cohomology of a direct image to cohomology on the source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open _root_.CategoryTheory.Abelian

universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

def abelianPullbackConstantIso :
    constantSheaf (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙ AbelianSheafPullback.Construction.abelianSheafPullback f ≅
      constantSheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ((constantSheafAdj (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop).comp
    (AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f)).leftAdjointUniq
      (constantSheafAdj (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)

local instance e40PushforwardSourceEnoughInjectives : EnoughInjectives (AbelianSheafInjectives.Construction.AbelianSheaves X) :=
  AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives X

local instance e40PushforwardSourceHasExt : HasExt.{u} (AbelianSheafInjectives.Construction.AbelianSheaves X) := hasExt_of_enoughInjectives _

local instance e40PushforwardTargetEnoughInjectives : EnoughInjectives (AbelianSheafInjectives.Construction.AbelianSheaves Y) :=
  AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives Y

local instance e40PushforwardTargetHasExt : HasExt.{u} (AbelianSheafInjectives.Construction.AbelianSheaves Y) := hasExt_of_enoughInjectives _

def abelianPushforwardCohomologyMap (F : AbelianSheafInjectives.Construction.AbelianSheaves X) (n : ℕ) :
    CategoryTheory.Sheaf.H ((AbelianSheafPullback.Construction.abelianSheafPushforward f).obj F) n →+ CategoryTheory.Sheaf.H F n :=
  (((((extFunctor n).mapIso ((abelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))).op).app F).symm).addCommGroupIsoToAddEquiv.toAddMonoidHom).comp
      (AdjunctionExtOne.Construction.adjunctionExtMap (AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f) _ F n)

theorem abelianPushforwardCohomologyMap_one_injective (F : AbelianSheafInjectives.Construction.AbelianSheaves X) :
    Function.Injective (abelianPushforwardCohomologyMap f F 1) := by
  exact (((((extFunctor 1).mapIso ((abelianPullbackConstantIso f).app
    (AddCommGrpCat.of (ULift.{u} ℤ))).op).app F).symm).addCommGroupIsoToAddEquiv.injective).comp
      (AdjunctionExtOne.Construction.adjunctionExtMap_one_injective (AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f) _ F)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction
