/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # General Dual Frame Scalar -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GeneralDualFrameScalar

open _root_.CategoryTheory Opposite
universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [∀ V, IsMulCommutative (R.obj.obj V)]
    (M : _root_.SheafOfModules R)

omit [∀ V, IsMulCommutative (R.obj.obj V)] in
theorem restrictTrivialization_scalar (U : C) (j : Over U)
    (e g : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (s : R.obj.obj (.op U))
    (h : g.hom = e.hom ≫ Dual.SheafOfModules.overUnitScalarEnd R U s) :
    (Dual.SheafOfModules.restrictOverTrivialization R M U g j).hom =
    (Dual.SheafOfModules.restrictOverTrivialization R M U e j).hom ≫
      Dual.SheafOfModules.overUnitScalarEnd R j.left (R.obj.map j.hom.op s) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let W := (Over.map j.hom).obj Z.unop
  have hx := ConcreteCategory.congr_hom
    (congrArg (fun q => q.val.app (.op W)) h) x
  erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hx
  erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply] at hx
  change g.hom.val.app (.op W) x =
    (show R.obj.obj (.op Z.unop.left) from e.hom.val.app (.op W) x) *
      R.obj.map Z.unop.hom.op (R.obj.map j.hom.op s)
  rw [← R.obj.map_comp_apply, ← op_comp]
  exact hx

theorem dualTrivialization_scalar (U : C)
    (e g : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (s : R.obj.obj (.op U))
    (h : g.hom = e.hom ≫ Dual.SheafOfModules.overUnitScalarEnd R U s)
    (alpha : M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) :
    Dual.SheafOfModules.dualTrivializationLinearEquiv R M U e alpha =
      s * Dual.SheafOfModules.dualTrivializationLinearEquiv R M U g alpha := by
  let T : Over U := Over.mk (𝟙 U)
  let oneU : (R.over U).obj.obj (.op T) := 1
  let sU : (R.over U).obj.obj (.op T) := s
  change (show (R.over U).obj.obj (.op T) from
      alpha.val.app (.op T) (e.inv.val.app (.op T) oneU)) =
    sU * (show (R.over U).obj.obj (.op T) from
      alpha.val.app (.op T) (g.inv.val.app (.op T) oneU))
  have he_one : e.hom.val.app (.op T) (e.inv.val.app (.op T) oneU) = oneU := by
    have hcomp := congrArg (fun q ↦ q.val.app (.op T)) e.inv_hom_id
    have happ := ConcreteCategory.congr_hom hcomp oneU
    erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at happ
    exact happ
  have hge : g.hom.val.app (.op T) (e.inv.val.app (.op T) oneU) = sU := by
    rw [h]
    erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    rw [he_one]
    erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply
      R U s (.op T) oneU]
    change (1 : R.obj.obj (.op U)) * R.obj.map (𝟙 (.op U)) s = s
    rw [R.obj.map_id]
    simp
  have hg_cancel (x : (M.over U).val.obj (.op T)) :
      g.inv.val.app (.op T) (g.hom.val.app (.op T) x) = x := by
    have hcomp := congrArg (fun q ↦ q.val.app (.op T)) g.hom_inv_id
    have happ := ConcreteCategory.congr_hom hcomp x
    erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at happ
    exact happ
  have hgen : e.inv.val.app (.op T) oneU =
      sU • g.inv.val.app (.op T) oneU := by
    calc
      e.inv.val.app (.op T) oneU =
          g.inv.val.app (.op T)
            (g.hom.val.app (.op T) (e.inv.val.app (.op T) oneU)) :=
        (hg_cancel (e.inv.val.app (.op T) oneU)).symm
      _ = g.inv.val.app (.op T) sU :=
        congrArg (fun x ↦ g.inv.val.app (.op T) x) hge
      _ = g.inv.val.app (.op T) (sU • oneU) := by
        congr 1
        change s = s * 1
        rw [mul_one]
      _ = sU • g.inv.val.app (.op T) oneU :=
        (g.inv.val.app (.op T)).hom.map_smul sU oneU
  rw [hgen, (alpha.val.app (.op T)).hom.map_smul]
  rfl

theorem dualFrame_scalar (U : C)
    (e g : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (s : R.obj.obj (.op U))
    (h : g.hom = e.hom ≫ Dual.SheafOfModules.overUnitScalarEnd R U s) :
    (Dual.SheafOfModules.dualOverIsoOfIso R M U e).hom =
      (Dual.SheafOfModules.dualOverIsoOfIso R M U g).hom ≫
        Dual.SheafOfModules.overUnitScalarEnd R U s := by
  apply _root_.SheafOfModules.hom_ext
  ext V alpha
  let eV := Dual.SheafOfModules.restrictOverTrivialization
    R M U e V.unop
  let gV := Dual.SheafOfModules.restrictOverTrivialization
    R M U g V.unop
  let sV : R.obj.obj (.op V.unop.left) :=
    R.obj.map V.unop.hom.op s
  have hV := restrictTrivialization_scalar R M U V.unop e g s h
  have hcoord := dualTrivialization_scalar
    R M V.unop.left eV gV sV hV alpha
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left eV alpha = _
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left eV alpha =
    (Dual.SheafOfModules.overUnitScalarEnd R U s).val.app V
      ((Dual.SheafOfModules.dualOverIsoOfIso
        R M U g).hom.val.app V alpha)
  erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply
    R U s V
      ((Dual.SheafOfModules.dualOverIsoOfIso
        R M U g).hom.val.app V alpha)]
  have hg : (Dual.SheafOfModules.dualOverIsoOfIso
      R M U g).hom.val.app V alpha =
    Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left gV alpha := by
    rfl
  rw [hg]
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left eV alpha =
    Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left gV alpha * sV
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left eV alpha =
    sV * Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left gV alpha at hcoord
  exact hcoord.trans (mul_comm' sV
    (Dual.SheafOfModules.dualTrivializationLinearEquiv
      R M V.unop.left gV alpha))

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GeneralDualFrameScalar
