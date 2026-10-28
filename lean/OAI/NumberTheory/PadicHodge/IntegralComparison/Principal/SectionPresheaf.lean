import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Sections
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Section Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf

noncomputable section

/-! The original ring and module sections on all principal subopens
of one affine open, with their actual restriction maps and ambient scalars. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

abbrev Index := AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U)
abbrev openSubset (r : Index U) := X.basicOpen r.val
abbrev inclusion (r : Index U) : openSubset U r ⟶ U := homOfLE (X.basicOpen_le r.val)
abbrev arrow {r s : Index U} (f : r ⟶ s) : openSubset U r ⟶ openSubset U s :=
  homOfLE ((AffinePrincipal.Diagram.functor X U hU).map f).le

def restrictionAlg {r s : Index U} (f : r ⟶ s) :
    Γ(X, openSubset U s) →ₐ[Γ(X, U)] Γ(X, openSubset U r) :=
  { (X.presheaf.map (arrow U hU f).op).hom with
    commutes' a := by
      change X.presheaf.map (arrow U hU f).op (X.presheaf.map (inclusion U s).op a) =
        X.presheaf.map (inclusion U r).op a
      rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
      rfl }

def rings : (Index U)ᵒᵖ ⥤ CommAlgCat.{u} Γ(X, U) where
  obj r := CommAlgCat.of Γ(X, U) Γ(X, openSubset U r.unop)
  map f := CommAlgCat.ofHom (restrictionAlg U hU f.unop)
  map_id r := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change X.presheaf.map (𝟙 (op (openSubset U r.unop))) x = x
    rw [X.presheaf.map_id]
    rfl
  map_comp f g := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change X.presheaf.map _ x = X.presheaf.map _ (X.presheaf.map _ x)
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl

instance sectionModule (M : X.Modules) (r : Index U) :
    Module Γ(X, U) Γ(M, openSubset U r) :=
  Module.compHom _ (algebraMap Γ(X, U) Γ(X, openSubset U r))

def moduleMap (M : X.Modules) {r s : Index U} (f : r ⟶ s) :
    Γ(M, openSubset U s) →ₗ[Γ(X, U)] Γ(M, openSubset U r) where
  toFun := M.presheaf.map (arrow U hU f).op
  map_add' := map_add _
  map_smul' a x := by
    change M.presheaf.map _ ((algebraMap Γ(X, U) Γ(X, openSubset U s) a) • x) = _
    rw [M.map_smul]
    exact congrArg (fun z => z • M.presheaf.map (arrow U hU f).op x)
      ((restrictionAlg U hU f).commutes a)

def modules (M : X.Modules) : (Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U) where
  obj r := ModuleCat.of Γ(X, U) Γ(M, openSubset U r.unop)
  map f := ModuleCat.ofHom (moduleMap U hU M f.unop)
  map_id r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.presheaf.map (𝟙 (op (openSubset U r.unop))) x = x
    rw [M.presheaf.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.presheaf.map _ x = M.presheaf.map _ (M.presheaf.map _ x)
    rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
    rfl

def moduleHom {M N : X.Modules} (f : M ⟶ N) : modules U hU M ⟶ modules U hU N where
  app r := ModuleCat.ofHom
    { toFun := f.val.app (op (openSubset U r.unop))
      map_add' := map_add _
      map_smul' a x := by
        change f.val.app (op (openSubset U r.unop))
          ((algebraMap Γ(X, U) Γ(X, openSubset U r.unop) a) • x) = _
        exact (f.val.app (op (openSubset U r.unop))).hom.map_smul _ _ }
  naturality r s a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (PresheafOfModules.naturality_apply f.val (arrow U hU a.unop).op x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
