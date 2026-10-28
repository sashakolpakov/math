import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictionCoefficientSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardSections

/-! # Basic Open Module Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasicOpenModuleRestriction

noncomputable section

/-! The actual restriction adjunction on a basic open agrees with section restriction over global coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤))

def basicOpenRestrictionModule : X.Modules :=
  (pushforward (X.basicOpen r).ι).obj (M.restrict (X.basicOpen r).ι)

def basicOpenRestrictionMap : Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M ⟶
    Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) (basicOpenRestrictionModule M r) :=
  (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor (RingHom.id Γ(X, ⊤))).map
    ((restrictAdjunction (X.basicOpen r).ι).unit.app M)

theorem basicOpen_image_preimage (U : X.Opens) :
    (X.basicOpen r).ι ''ᵁ ((X.basicOpen r).ι ⁻¹ᵁ U) =
      X.basicOpen (X.presheaf.map U.leTop.op r) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    X.basicOpen_res, inf_comm]

def basicOpenRestrictionAppIso (U : X.Opens) :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) (basicOpenRestrictionModule M r)).obj (op U) ≅
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).obj
        (op (X.basicOpen (X.presheaf.map U.leTop.op r))) :=
  (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv (X.basicOpen r).ι (RingHom.id Γ(X, ⊤))
    (M.restrict (X.basicOpen r).ι) U).toModuleIso ≪≫
  Open.RestrictionCoefficientSections.coefficientOpenRestrictionSectionIso (X.basicOpen r).ι (RingHom.id Γ(X, ⊤)) M
    ((X.basicOpen r).ι ⁻¹ᵁ U) ≪≫
  (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).mapIso
    (eqToIso (basicOpen_image_preimage r U).symm).op

theorem basicOpenRestrictionMap_app_iso (U : X.Opens) :
    (basicOpenRestrictionMap M r).app (op U) ≫ (basicOpenRestrictionAppIso M r U).hom =
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map
      (homOfLE (X.basicOpen_le (X.presheaf.map U.leTop.op r))).op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let x' : Γ(M, U) := x
  change M.presheaf.map (eqToIso (basicOpen_image_preimage r U).symm).op.hom
    (M.presheaf.map (homOfLE ((X.basicOpen r).ι.image_preimage_le U)).op x') =
    M.presheaf.map (homOfLE (X.basicOpen_le (X.presheaf.map U.leTop.op r))).op x'
  rw [← M.presheaf.map_comp_apply]
  rfl

def basicOpenRestrictionTopIso :
    (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) (basicOpenRestrictionModule M r)).obj (op ⊤) ≅
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).obj (op (X.basicOpen r)) :=
  (Coefficient.PushforwardSections.coefficientPushforwardSectionEquiv (X.basicOpen r).ι (RingHom.id Γ(X, ⊤))
    (M.restrict (X.basicOpen r).ι) ⊤).toModuleIso ≪≫
  Open.RestrictionCoefficientSections.coefficientOpenRestrictionSectionIso (X.basicOpen r).ι (RingHom.id Γ(X, ⊤)) M ⊤ ≪≫
  (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).mapIso
    (eqToIso (X.basicOpen r).ι_image_top.symm).op

theorem basicOpenRestrictionMap_top_iso :
    (basicOpenRestrictionMap M r).app (op ⊤) ≫ (basicOpenRestrictionTopIso M r).hom =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf (RingHom.id Γ(X, ⊤)) M).map (X.basicOpen r).leTop.op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let x' : Γ(M, ⊤) := x
  change M.presheaf.map (eqToIso (X.basicOpen r).ι_image_top.symm).op.hom
    (M.presheaf.map ((X.basicOpen r).ι ''ᵁ (⊤ : (X.basicOpen r).toScheme.Opens)).leTop.op x') =
    M.presheaf.map (X.basicOpen r).leTop.op x'
  rw [← M.presheaf.map_comp_apply]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BasicOpenModuleRestriction
