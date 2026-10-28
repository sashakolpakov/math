import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdjunctionExtNaturality
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology

/-! # Pushforward Cohomology Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PushforwardCohomologyNaturality

noncomputable section

/-! The actual comparison from direct-image cohomology to source
cohomology commutes with maps of coefficient sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

local instance pushforwardNaturality_sourceInjectives : EnoughInjectives (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives X
local instance pushforwardNaturality_sourceExt : HasExt.{0} (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X) :=
  hasExt_of_enoughInjectives _
local instance pushforwardNaturality_targetInjectives : EnoughInjectives (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.abelianSheaves_enoughInjectives Y
local instance pushforwardNaturality_targetExt : HasExt.{0} (ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves Y) :=
  hasExt_of_enoughInjectives _

theorem abelianPushforwardCohomologyMap_natural
    {F G : ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafInjectives.Construction.AbelianSheaves X} (a : F ⟶ G) (n : ℕ)
    (x : CategoryTheory.Sheaf.H ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).obj F) n) :
    ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPushforwardCohomologyMap f G n
        (CategoryTheory.Sheaf.H.map ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).map a) n x) =
      CategoryTheory.Sheaf.H.map a n (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPushforwardCohomologyMap f F n x) := by
  let P := (constantSheaf (_root_.Opens.grothendieckTopology Y) AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ))
  let e := (ArithmeticGeometry.OrdinaryLocus.Openness.PushforwardCohomology.Construction.abelianPullbackConstantIso f).app (AddCommGrpCat.of (ULift ℤ))
  let adj := ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPullbackAdjunction f
  change (Ext.mk₀ e.inv).comp
      (ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction.adjunctionExtMap adj P G n
        (x.comp (Ext.mk₀ ((ArithmeticGeometry.OrdinaryLocus.Openness.AbelianSheafPullback.Construction.abelianSheafPushforward f).map a)) (add_zero n))) (zero_add n) =
    ((Ext.mk₀ e.inv).comp (ArithmeticGeometry.OrdinaryLocus.Openness.AdjunctionExtOne.Construction.adjunctionExtMap adj P F n x) (zero_add n)).comp (Ext.mk₀ a) (add_zero n)
  rw [AdjunctionExtNaturality.adjunctionExtMap_natural, Ext.comp_assoc_of_third_deg_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PushforwardCohomologyNaturality
