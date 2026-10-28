import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections

/-! # Dual Frame Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameRestriction

/-! The native dual frame is the image of its over-site frame. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem dualRestrictionFrame_eq {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M U e =
      FrameSections.restrictTrivializationOfOverIso (Dual.Scheme.Modules.dualObj M) U
        (Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U
          (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)) := rfl

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameRestriction
