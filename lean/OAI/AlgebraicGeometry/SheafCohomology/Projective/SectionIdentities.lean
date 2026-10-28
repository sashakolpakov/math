/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/Picard/DualPullback/UnitComp.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Evaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionUnit
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOne

/-! # Section Identities -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionIdentities

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-! Component identities for module isomorphisms and chosen section maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory Opposite
universe u
namespace Scheme.Modules

noncomputable def topSectionHom {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) : Invertible.Scheme.Modules.unitObj X ⟶ M :=
  M.unitHomEquiv.symm (AffineRankOne.globalSectionFamily M x)

@[simp]
theorem topSectionHom_app_top_apply_one {X : Scheme.{u}} (M : X.Modules)
    (x : Γ(M, (⊤ : X.Opens))) :
    (topSectionHom M x).val.app (op ⊤) (show Γ(X, ⊤) from 1) = x := by
  change (AffineRankOne.globalGeneratorHom M x).val.app (op ⊤)
    (show Γ(X, ⊤) from 1) = x
  rw [AffineRankOne.globalGeneratorHom_top, one_smul]

theorem restrictUnitIso_inv_app_applyP {A B : Scheme.{u}} (g : A ⟶ B)
    [IsOpenImmersion g] (W : A.Opens) (x : Γ(A, W)) :
    ((restrictUnitIso g).inv.val.app (op W)).hom' x = (g.appIso W).inv x := rfl

theorem iso_inv_hom_app_applyT {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opensᵒᵖ) (x : N.val.obj U) :
    e.hom.val.app U (e.inv.val.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun f => f.val.app U) e.inv_hom_id) x

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem dualOverIsoOfIso_inv_terminal_apply_oneT {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (Dual.SheafOfModules.dualOverIsoOfIso
      X.ringCatSheaf M U e).inv.val.app
        (op (Over.mk (𝟙 U))) (show Γ(X, U) from 1) = e.hom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (show Γ(X, W.unop.left) from e.hom.val.app W x) *
    X.presheaf.map W.unop.hom.op 1 = e.hom.val.app W x
  rw [map_one, mul_one]

end Scheme.Modules

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SectionIdentities
