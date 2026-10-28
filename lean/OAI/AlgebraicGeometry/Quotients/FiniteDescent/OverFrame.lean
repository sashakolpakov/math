import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOpenFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition

/-! # Over Frame -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverFrame

noncomputable section

/-! Scalar transition formulas for dual frames and their sections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

namespace Construction.OverFrameTransitions

variable {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
variable (hU : W ≤ U) (hV : W ≤ V)
variable (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
variable (f : M.over V ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over V))

local instance (Y : Scheme.{u}) :
    ∀ A, IsMulCommutative (Y.ringCatSheaf.obj.obj A) := fun A => by
  change IsMulCommutative (Y.presheaf.obj A)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem dual (r : Γ(X, W))
    (h : (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M V f (Over.mk (homOfLE hV))).hom =
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U e (Over.mk (homOfLE hU))).hom ≫
          SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W r) :
    (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M) U
      (SheafCohomology.Projective.Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U e)
      (Over.mk (homOfLE hU))).hom =
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M) V
        (SheafCohomology.Projective.Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M V f)
        (Over.mk (homOfLE hV))).hom ≫
          SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W r := by
  rw [SheafCohomology.Projective.DualOpenFrames.dualOverFrame_restrict, SheafCohomology.Projective.DualOpenFrames.dualOverFrame_restrict]
  exact SheafCohomology.Projective.OverFrameTransitions.dualOverIsoOfIso_hom_eq_comp_scalar M W _ _ r h

theorem sections (a : Γ(X, U)) (b : Γ(X, V)) (r : Γ(X, W))
    (h : SheafCohomology.Projective.DualFrameTransition.FrameTransition (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M U e (Over.mk (homOfLE hU)))
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M V f (Over.mk (homOfLE hV)))
          (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W r))
    (hab : X.presheaf.map (homOfLE hU).op a = X.presheaf.map (homOfLE hV).op b * r) :
    M.presheaf.map (homOfLE hU).op (SheafCohomology.Projective.FrameSections.overTrivializationSection M U e a) =
      M.presheaf.map (homOfLE hV).op (SheafCohomology.Projective.FrameSections.overTrivializationSection M V f b) := by
  rw [SheafCohomology.Projective.FrameSections.overTrivializationSection_restrict, SheafCohomology.Projective.FrameSections.overTrivializationSection_restrict]
  exact SheafCohomology.Projective.FrameSections.overTrivializationSection_eq_of_transition M W _ _ r _ _ h hab

theorem dual_chosen
    (a : (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M).over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (b : (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M).over V ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over V))
    (ha : a = SheafCohomology.Projective.Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U e)
    (hb : b = SheafCohomology.Projective.Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M V f)
    (r : Γ(X, W))
    (h : (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M V f (Over.mk (homOfLE hV))).hom =
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U e (Over.mk (homOfLE hU))).hom ≫
          SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W r) :
    SheafCohomology.Projective.DualFrameTransition.FrameTransition
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M) U a (Over.mk (homOfLE hU)))
      (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf (SheafCohomology.Projective.Dual.Scheme.Modules.dualObj M) V b (Over.mk (homOfLE hV)))
      (SheafCohomology.Projective.Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W r) := by
  rw [ha, hb]
  exact dual M hU hV e f r h

end Construction.OverFrameTransitions

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.OverFrame
