import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOpenFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GeneralDualFrameScalar

/-! # Dual Overlap Transition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOverlapTransition

noncomputable section

/-! Dual scalar transitions on an intersection of two trivializing opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem dualOpenOverlap_transition {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : M.restrict V.ι ≅ Invertible.Scheme.Modules.unitObj V.toScheme)
    (s : Γ(X, W))
    (h : (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M V
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M V g)
      (Over.mk (homOfLE hWV))).hom =
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
        (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)
        (Over.mk (homOfLE hWU))).hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W s) :
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization hWU
      (Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M U e)).hom =
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization hWV
      (Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M V g)).hom ≫
      UnitScalar.unitEndomorphismOfTopSection (OpenFrames.Scheme.Modules.openTopSection W s) := by
  rw [DualOpenFrames.restrictOpenTrivialization_dualRestrictIsoOfRestrictIso,
    DualOpenFrames.restrictOpenTrivialization_dualRestrictIsoOfRestrictIso]
  apply OverScalarRestriction.restrictTrivializationOfOverIso_hom_eq_comp_scalar
  exact GeneralDualFrameScalar.dualFrame_scalar X.ringCatSheaf M W _ _ s h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOverlapTransition
