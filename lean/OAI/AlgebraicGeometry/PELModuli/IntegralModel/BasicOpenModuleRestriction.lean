import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.OpenBaseLocalization
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseModule
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechPushforward

/-! # Basic Open Module Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenModuleRestriction

noncomputable section

/-! The adjunction unit for restriction to a basic open is the actual
section restriction, compatibly with global scalar multiplication. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def baseModuleSheafMap {X B : Scheme.{u}} (f : X ⟶ B)
    {M N : X.Modules} (a : M ⟶ N) :
    Quotients.FiniteDescent.BaseModule.Construction.BaseModuleSheaf.sheaf f M ⟶ Quotients.FiniteDescent.BaseModule.Construction.BaseModuleSheaf.sheaf f N :=
  ⟨(SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor f).map a⟩

variable {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤))

def basicOpenRestrictionModule : X.Modules :=
  (pushforward (X.basicOpen r).ι).obj (M.restrict (X.basicOpen r).ι)

def basicOpenRestrictionMap : Quotients.FiniteDescent.BaseModule.Construction.BaseModuleSheaf.sheaf (𝟙 X) M ⟶
    Quotients.FiniteDescent.BaseModule.Construction.BaseModuleSheaf.sheaf (𝟙 X) (basicOpenRestrictionModule M r) :=
  baseModuleSheafMap (𝟙 X) ((restrictAdjunction (X.basicOpen r).ι).unit.app M)

theorem basicOpen_image_preimage (U : X.Opens) :
    (X.basicOpen r).ι ''ᵁ ((X.basicOpen r).ι ⁻¹ᵁ U) =
      X.basicOpen (X.presheaf.map U.leTop.op r) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    X.basicOpen_res, inf_comm]

def basicOpenRestrictionAppIso (U : X.Opens) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) (basicOpenRestrictionModule M r)).obj (op U) ≅
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).obj
        (op (X.basicOpen (X.presheaf.map U.leTop.op r))) :=
  (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseModulePresheafPushforwardAppIso (X.basicOpen r).ι (𝟙 X)
    (M.restrict (X.basicOpen r).ι) U).symm ≪≫
  SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafRestrictAppIso (𝟙 X) (X.basicOpen r).ι M
    ((X.basicOpen r).ι ⁻¹ᵁ U) ≪≫
  (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).mapIso (eqToIso (basicOpen_image_preimage r U).symm).op

theorem basicOpenRestrictionMap_app_iso (U : X.Opens) :
    (basicOpenRestrictionMap M r).hom.app (op U) ≫
      (basicOpenRestrictionAppIso M r U).hom =
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).map
      (homOfLE (X.basicOpen_le (X.presheaf.map U.leTop.op r))).op := by
  apply ModuleCat.hom_ext
  ext x
  change M.presheaf.map (eqToIso (basicOpen_image_preimage r U).symm).op.hom
    (M.presheaf.map (homOfLE ((X.basicOpen r).ι.image_preimage_le U)).op x) =
    M.presheaf.map (homOfLE (X.basicOpen_le (X.presheaf.map U.leTop.op r))).op x
  rw [← M.presheaf.map_comp_apply]
  rfl

def basicOpenRestrictionTopIso :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) (basicOpenRestrictionModule M r)).obj (op ⊤) ≅
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).obj (op (X.basicOpen r)) :=
  (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseModulePresheafPushforwardAppIso (X.basicOpen r).ι (𝟙 X)
    (M.restrict (X.basicOpen r).ι) ⊤).symm ≪≫
  SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafRestrictAppIso (𝟙 X) (X.basicOpen r).ι M ⊤ ≪≫
  (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).mapIso (eqToIso (X.basicOpen r).ι_image_top.symm).op

theorem basicOpenRestrictionMap_top_iso :
    (basicOpenRestrictionMap M r).hom.app (op ⊤) ≫
      (basicOpenRestrictionTopIso M r).hom =
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).map (X.basicOpen r).leTop.op := by
  apply ModuleCat.hom_ext
  ext x
  let x' : Γ(M, ⊤) := x
  change M.presheaf.map (eqToIso (X.basicOpen r).ι_image_top.symm).op.hom
    (M.presheaf.map ((X.basicOpen r).ι ''ᵁ (⊤ : (X.basicOpen r).toScheme.Opens)).leTop.op x') =
    M.presheaf.map (X.basicOpen r).leTop.op x'
  rw [← M.presheaf.map_comp_apply]
  rfl

theorem basicOpenRestrictionMap_affine_isLocalized [M.IsQuasicoherent]
    (U : X.affineOpens) :
    IsLocalizedModule.Away r ((basicOpenRestrictionMap M r).hom.app (op U.1)).hom := by
  let a := ((basicOpenRestrictionMap M r).hom.app (op U.1)).hom
  let e := (basicOpenRestrictionAppIso M r U.1).toLinearEquiv
  have ha : e.toLinearMap.comp a =
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).map
        (homOfLE (X.basicOpen_le (X.presheaf.map U.1.leTop.op r))).op).hom :=
    congrArg ModuleCat.Hom.hom (basicOpenRestrictionMap_app_iso M r U.1)
  have hloc : IsLocalizedModule.Away r (e.toLinearMap.comp a) :=
    ha.symm ▸ Affine.OpenBaseLocalization.affineOpen_baseSection_isLocalized M U r
  let := hloc
  have hback := IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
    (e.toLinearMap.comp a) e.symm
  have he : e.symm.toLinearMap.comp (e.toLinearMap.comp a) = a := by
    ext x
    exact e.symm_apply_apply (a x)
  rw [he] at hback
  exact hback

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenModuleRestriction
