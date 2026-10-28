import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Closed Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars

noncomputable section

/-! The actual sections on inverse images of ambient principal opens
form a diagram over the sections on the inverse image of the original
open. Restriction of scalars recovers the original pushforward diagram.
The construction applies, in particular, to the closed immersions used
in the principal residue calculation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X Z : Scheme.{u}} (i : X ⟶ Z) (U : Z.Opens) (hU : IsAffineOpen U)

abbrev pullbackOpen (r : SectionPresheaf.Index U) := i ⁻¹ᵁ SectionPresheaf.openSubset U r
abbrev pullbackInclusion (r : SectionPresheaf.Index U) : pullbackOpen i U r ⟶ i ⁻¹ᵁ U :=
  homOfLE (i.preimage_mono (Z.basicOpen_le r.val))
abbrev pullbackArrow {r s : SectionPresheaf.Index U} (a : r ⟶ s) :
    pullbackOpen i U r ⟶ pullbackOpen i U s :=
  homOfLE (i.preimage_mono (SectionPresheaf.arrow U hU a).le)

instance sectionAlgebra (r : SectionPresheaf.Index U) :
    Algebra Γ(X, i ⁻¹ᵁ U) Γ(X, pullbackOpen i U r) :=
  (X.presheaf.map (pullbackInclusion i U r).op).hom.toAlgebra

def restrictionAlg {r s : SectionPresheaf.Index U} (a : r ⟶ s) :
    Γ(X, pullbackOpen i U s) →ₐ[Γ(X, i ⁻¹ᵁ U)] Γ(X, pullbackOpen i U r) :=
  { (X.presheaf.map (pullbackArrow i U hU a).op).hom with
    commutes' x := by
      change X.presheaf.map (pullbackArrow i U hU a).op
          (X.presheaf.map (pullbackInclusion i U s).op x) =
        X.presheaf.map (pullbackInclusion i U r).op x
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
      rfl }

def rings : (SectionPresheaf.Index U)ᵒᵖ ⥤ CommAlgCat.{u} Γ(X, i ⁻¹ᵁ U) where
  obj r := CommAlgCat.of Γ(X, i ⁻¹ᵁ U) Γ(X, pullbackOpen i U r.unop)
  map a := CommAlgCat.ofHom (restrictionAlg i U hU a.unop)
  map_id r := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change X.presheaf.map (𝟙 (op (pullbackOpen i U r.unop))) x = x
    rw [X.presheaf.map_id]
    rfl
  map_comp a b := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change X.presheaf.map _ x = X.presheaf.map _ (X.presheaf.map _ x)
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl

instance sectionModule (M : X.Modules) (r : SectionPresheaf.Index U) :
    Module Γ(X, i ⁻¹ᵁ U) Γ(M, pullbackOpen i U r) :=
  Module.compHom _ (algebraMap Γ(X, i ⁻¹ᵁ U) Γ(X, pullbackOpen i U r))

instance sectionTower (M : X.Modules) (r : SectionPresheaf.Index U) :
    IsScalarTower Γ(X, i ⁻¹ᵁ U) Γ(X, pullbackOpen i U r) Γ(M, pullbackOpen i U r) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def moduleMap (M : X.Modules) {r s : SectionPresheaf.Index U} (a : r ⟶ s) :
    Γ(M, pullbackOpen i U s) →ₗ[Γ(X, i ⁻¹ᵁ U)] Γ(M, pullbackOpen i U r) where
  toFun := M.presheaf.map (pullbackArrow i U hU a).op
  map_add' := map_add _
  map_smul' x m := by
    change M.presheaf.map _
      ((algebraMap Γ(X, i ⁻¹ᵁ U) Γ(X, pullbackOpen i U s) x) • m) = _
    rw [M.map_smul]
    exact congrArg (fun z => z • M.presheaf.map (pullbackArrow i U hU a).op m)
      ((restrictionAlg i U hU a).commutes x)

def modules (M : X.Modules) : (SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, i ⁻¹ᵁ U) where
  obj r := ModuleCat.of Γ(X, i ⁻¹ᵁ U) Γ(M, pullbackOpen i U r.unop)
  map a := ModuleCat.ofHom (moduleMap i U hU M a.unop)
  map_id r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.presheaf.map (𝟙 (op (pullbackOpen i U r.unop))) x = x
    rw [M.presheaf.map_id]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.presheaf.map _ x = M.presheaf.map _ (M.presheaf.map _ x)
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
    rfl

def moduleHom {M N : X.Modules} (f : M ⟶ N) : modules i U hU M ⟶ modules i U hU N where
  app r := ModuleCat.ofHom
    { toFun := f.val.app (op (pullbackOpen i U r.unop))
      map_add' := map_add _
      map_smul' a x := by
        change f.val.app (op (pullbackOpen i U r.unop))
          ((algebraMap Γ(X, i ⁻¹ᵁ U) Γ(X, pullbackOpen i U r.unop) a) • x) = _
        exact (f.val.app (op (pullbackOpen i U r.unop))).hom.map_smul _ _ }
  naturality r s a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact PresheafOfModules.naturality_apply f.val (pullbackArrow i U hU a.unop).op x

theorem scalar_square (r : SectionPresheaf.Index U) (a : Γ(Z, U)) :
    X.presheaf.map (pullbackInclusion i U r).op (i.app U a) =
      i.app (SectionPresheaf.openSubset U r) (Z.presheaf.map (SectionPresheaf.inclusion U r).op a) :=
  (ConcreteCategory.congr_hom (i.naturality (SectionPresheaf.inclusion U r).op) a).symm

def restrictionEquiv (M : X.Modules) (r : SectionPresheaf.Index U) :
    (ModuleCat.restrictScalars (i.app U).hom).obj ((modules i U hU M).obj (op r)) ≃ₗ[Γ(Z, U)]
      (SectionPresheaf.modules U hU ((Scheme.Modules.pushforward i).obj M)).obj (op r) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change Γ(M, pullbackOpen i U r) at x
    change X.presheaf.map (pullbackInclusion i U r).op (i.app U a) • x =
      i.app (SectionPresheaf.openSubset U r) (Z.presheaf.map (SectionPresheaf.inclusion U r).op a) • x
    exact congrArg (fun z : Γ(X, pullbackOpen i U r) => z • x) (scalar_square i U r a)

def restrictionIso (M : X.Modules) :
    modules i U hU M ⋙ ModuleCat.restrictScalars (i.app U).hom ≅
      SectionPresheaf.modules U hU ((Scheme.Modules.pushforward i).obj M) :=
  NatIso.ofComponents (fun r => (restrictionEquiv i U hU M r.unop).toModuleIso)
    (fun {_ _} _ => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

theorem restrictionIso_hom_app (M : X.Modules) (r : SectionPresheaf.Index U)
    (x : Γ(M, pullbackOpen i U r)) :
    ((restrictionIso i U hU M).hom.app (op r)) x = x := rfl

theorem restrictionIso_natural {M N : X.Modules} (f : M ⟶ N) :
    Functor.whiskerRight (moduleHom i U hU f) (ModuleCat.restrictScalars (i.app U).hom) ≫
        (restrictionIso i U hU N).hom =
      (restrictionIso i U hU M).hom ≫
        SectionPresheaf.moduleHom U hU ((Scheme.Modules.pushforward i).map f) := by
  ext r x
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedScalars
