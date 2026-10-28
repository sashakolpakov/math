import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ChangeOfLeftAdjoint
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.BaseChangeMate
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeMateIdentification

/-! # Canonical Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CanonicalBaseChange

noncomputable section

/-! The canonical module and structure-sheaf base-change maps are isomorphisms for restriction to an open subscheme of the base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)

theorem openModuleBaseChange_comparison (M : X.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
        ((Scheme.Modules.pushforward f).obj M) ≫
      (SchemeModule.SchemeModuleBaseChange.map (isPullback_morphismRestrict f U).flip).app M =
    (OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U).app M ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).hom.app M) :=
  ChangeOfLeftAdjoint.MateChange.leftAdjointUniq_compatibility
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι)
    (Scheme.Modules.restrictAdjunction U.ι)
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι)
    (OpenModule.BaseChangeMate.OpenPullbackSquare.pushforwardSquareIso f U).hom M

theorem openModuleBaseChange_isIso (M : X.Modules) :
    IsIso ((SchemeModule.SchemeModuleBaseChange.map (isPullback_morphismRestrict f U).flip).app M) := by
  have := OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap_isIso f U
  have hi : IsIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
          ((Scheme.Modules.pushforward f).obj M) ≫
        (SchemeModule.SchemeModuleBaseChange.map (isPullback_morphismRestrict f U).flip).app M) := by
    rw [openModuleBaseChange_comparison]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

theorem openStructureBaseChange_isIso :
    IsIso (Structure.SheafBaseChange.structureBaseChangeMap (isPullback_morphismRestrict f U).flip) := by
  rw [Structure.BaseChangeMateIdentification.structureBaseChangeMap_eq_mate]
  have := openModuleBaseChange_isIso f U (Line.Bundles.structureModule X)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CanonicalBaseChange
