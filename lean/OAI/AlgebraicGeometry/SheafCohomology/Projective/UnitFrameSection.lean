import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections

/-! # Unit Frame Section -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitFrameSection

noncomputable section

/-! The canonical unit section has coefficient one in the restricted unit frame. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem localTrivializationTopSection_monoidalUnitSection
    {X : Scheme.{u}} (U : X.affineOpens) :
    FrameSections.localTrivializationTopSection (𝟙_ X.Modules) U
      (TensorSections.restrictMonoidalUnitIso U.1.ι ≪≫ TensorSections.monoidalUnitObjIso U.1.toScheme)
      (TensorSections.monoidalUnitSection X) = (1 : Γ(U.1.toScheme, ⊤)) := by
  let F := Scheme.Modules.restrictFunctor U.1.ι
  have he : (TensorSections.restrictMonoidalUnitIso U.1.ι ≪≫ TensorSections.monoidalUnitObjIso U.1.toScheme).hom =
      F.map (TensorSections.monoidalUnitObjIso X).hom ≫ (Scheme.Modules.restrictUnitIso U.1.ι).hom :=
    (TensorFrameSections.poleTensor_restrict_monoidalUnitObjIso U.1.ι).symm
  unfold FrameSections.localTrivializationTopSection
  rw [he]
  erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [← FrameSections.localTrivializationRestriction_map]
  have h1 : (TensorSections.monoidalUnitObjIso X).hom.val.app (op ⊤) (TensorSections.monoidalUnitSection X) =
      (show Γ(X, ⊤) from 1) :=
    SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT (TensorSections.monoidalUnitObjIso X) (op ⊤)
      (show Γ(X, ⊤) from 1)
  rw [h1]
  change (U.1.ι.appIso ⊤).hom
    (X.presheaf.map (eqToHom U.1.ι_image_top).op
      (X.presheaf.map U.1.leTop.op 1)) = 1
  simp only [map_one]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitFrameSection
