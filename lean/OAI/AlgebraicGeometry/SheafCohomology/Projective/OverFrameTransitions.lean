/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealOverFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections

/-! # Over Frame Transitions -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions

open _root_.AlgebraicGeometry _root_.CategoryTheory Limits _root_.SheafOfModules _root_.TopologicalSpace
universe u

/-- An equation expressing an ideal generator in an over-site trivialization
restricts to the corresponding equation for the restricted generator. -/
theorem restrictOverTrivialization_inv_comp_over
    {X : Scheme.{u}} {M : X.Modules}
    (i : M ⟶ Invertible.Scheme.Modules.unitObj X) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.inv ≫ i.over U =
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    {V : X.Opens} (hVU : V ≤ U) :
    let j : Over U := Over.mk (homOfLE hVU)
    let eV := Dual.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M U e j
    eV.inv ≫ i.over V =
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
        (X.presheaf.map (homOfLE hVU).op r) := by
  dsimp only
  let j : Over U := Over.mk (homOfLE hVU)
  let eV := Dual.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U e j
  change eV.inv ≫ i.over V =
    Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
      (X.presheaf.map (homOfLE hVU).op r)
  apply SheafOfModules.hom_ext
  ext Z
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have heV : eV.inv.val.app Z
      (show (X.ringCatSheaf.over V).obj.obj Z from 1) =
        e.inv.val.app (.op ((Over.map j.hom).obj Z.unop))
          (show (X.ringCatSheaf.over V).obj.obj Z from 1) :=
    Dual.SheafOfModules.restrictOverTrivialization_inv_app_apply
      X.ringCatSheaf M U e j Z
        (show (X.ringCatSheaf.over V).obj.obj Z from 1)
  rw [heV]
  have happ := congrArg (fun q ↦ q.val.app
    (.op ((Over.map j.hom).obj Z.unop))) h
  have hx := ConcreteCategory.congr_hom happ
    (show (X.ringCatSheaf.over U).obj.obj
      (.op ((Over.map j.hom).obj Z.unop)) from 1)
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hx
  change i.val.app (.op Z.unop.left)
      (e.inv.val.app (.op ((Over.map j.hom).obj Z.unop))
        (show (X.ringCatSheaf.over U).obj.obj
          (.op ((Over.map j.hom).obj Z.unop)) from 1)) =
    (1 : X.presheaf.obj (.op Z.unop.left)) *
      X.presheaf.map Z.unop.hom.op
        (X.presheaf.map (homOfLE hVU).op r)
  change i.val.app (.op ((Over.map j.hom).obj Z.unop).left)
      (e.inv.val.app (.op ((Over.map j.hom).obj Z.unop))
        (show (X.ringCatSheaf.over U).obj.obj
          (.op ((Over.map j.hom).obj Z.unop)) from 1)) =
    (1 : X.presheaf.obj (.op ((Over.map j.hom).obj Z.unop).left)) *
      X.presheaf.map ((Over.map j.hom).obj Z.unop).hom.op r at hx
  have hmap : X.presheaf.map Z.unop.hom.op
      (X.presheaf.map (homOfLE hVU).op r) =
    X.presheaf.map ((Over.map j.hom).obj Z.unop).hom.op r := by
    have hc := congrArg (fun φ ↦ CommRingCat.Hom.hom φ r)
      ((X.presheaf.map_comp (homOfLE hVU).op Z.unop.hom.op).symm)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hc
    refine hc.trans ?_
    exact congrArg (fun ψ ↦ (CommRingCat.Hom.hom (X.presheaf.map ψ)) r)
      (Subsingleton.elim _ _)
  rw [hmap]
  exact hx

section

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- If two trivializations differ by multiplication by `s`, then their dual
coordinates differ by multiplication by `s` in the opposite direction. -/
theorem dualTrivializationLinearEquiv_eq_mul_of_transition
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : g.hom = e.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s)
    (alpha : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (show Γ(X, U) from
      Dual.SheafOfModules.dualTrivializationLinearEquiv X.ringCatSheaf M U e alpha) =
      s * (show Γ(X, U) from
        Dual.SheafOfModules.dualTrivializationLinearEquiv
          X.ringCatSheaf M U g alpha) := by
  let T : Over U := Over.mk (𝟙 U)
  let oneU : (X.ringCatSheaf.over U).obj.obj (.op T) := 1
  let sU : (X.ringCatSheaf.over U).obj.obj (.op T) := s
  change (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      alpha.val.app (.op T) (e.inv.val.app (.op T) oneU)) =
    sU * (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      alpha.val.app (.op T) (g.inv.val.app (.op T) oneU))
  have he_one : e.hom.val.app (.op T) (e.inv.val.app (.op T) oneU) = oneU := by
    have hcomp := congrArg (fun q ↦ q.val.app (.op T)) e.inv_hom_id
    have happ := ConcreteCategory.congr_hom hcomp oneU
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at happ
    exact happ
  have hge : g.hom.val.app (.op T) (e.inv.val.app (.op T) oneU) = sU := by
    rw [h]
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply]
    rw [he_one]
    erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply
      X.ringCatSheaf U s (.op T) oneU]
    change (1 : Γ(X, U)) * X.presheaf.map (𝟙 (.op U)) s = s
    rw [X.presheaf.map_id]
    simp
  have hg_cancel (x : (M.over U).val.obj (.op T)) :
      g.inv.val.app (.op T) (g.hom.val.app (.op T) x) = x := by
    have hcomp := congrArg (fun q ↦ q.val.app (.op T)) g.hom_inv_id
    have happ := ConcreteCategory.congr_hom hcomp x
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
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

/-- A scalar transition between frames restricts by restricting its scalar. -/
theorem restrictOverTrivialization_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e g : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : g.hom = e.hom ≫ Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) :
    (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U g
      (Over.mk (homOfLE hVU))).hom =
    (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
      (Over.mk (homOfLE hVU))).hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V
        (X.presheaf.map (homOfLE hVU).op s) := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let W := (Over.map (homOfLE hVU)).obj Z.unop
  have hx := ConcreteCategory.congr_hom
    (congrArg (fun q => q.val.app (.op W)) h) x
  erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hx
  erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply] at hx
  change g.hom.val.app (.op W) x =
    (show Γ(X, Z.unop.left) from e.hom.val.app (.op W) x) * X.presheaf.map Z.unop.hom.op
      (X.presheaf.map (homOfLE hVU).op s)
  rw [← X.presheaf.map_comp_apply]
  exact hx

/-- Dualization reverses a scalar transition between trivializations. -/
theorem dualOverIsoOfIso_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : g.hom = e.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) :
    (Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U e).hom =
      (Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U g).hom ≫
        Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s := by
  apply SheafOfModules.hom_ext
  ext V alpha
  let eV := Dual.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U e V.unop
  let gV := Dual.SheafOfModules.restrictOverTrivialization
    X.ringCatSheaf M U g V.unop
  let sV : X.ringCatSheaf.obj.obj (.op V.unop.left) :=
    X.presheaf.map V.unop.hom.op s
  have hV : gV.hom = eV.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf V.unop.left sV := by
    have hV' := restrictOverTrivialization_hom_eq_comp_scalar
      M (leOfHom V.unop.hom) e g s h
    convert hV' using 1
    all_goals rfl
  have hcoord := dualTrivializationLinearEquiv_eq_mul_of_transition
    M V.unop.left eV gV sV hV alpha
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha = _
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha =
    (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s).val.app V
      ((Dual.SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U g).hom.val.app V alpha)
  erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply
    X.ringCatSheaf U s V
      ((Dual.SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U g).hom.val.app V alpha)]
  have hg : (Dual.SheafOfModules.dualOverIsoOfIso
      X.ringCatSheaf M U g).hom.val.app V alpha =
    Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha := by
    rfl
  rw [hg]
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha =
    Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha * sV
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left eV alpha =
    sV * Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha at hcoord
  exact hcoord.trans (mul_comm' sV
    (Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M V.unop.left gV alpha))

end

/-- Restricting a module monomorphism to an over-site remains a monomorphism. -/
theorem sheafOfModules_mono_over
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : _root_.SheafOfModules R}
    (f : M ⟶ N) (hf : Mono f) (U : C) : Mono (f.over U) := by
  have := hf
  apply (_root_.SheafOfModules.forget (R.over U)).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro V
  have : Mono ((_root_.SheafOfModules.forget R).map f) :=
    Functor.map_mono (_root_.SheafOfModules.forget R) f
  exact PresheafOfModules.injective_of_mono
    ((_root_.SheafOfModules.forget R).map f) (.op V.unop.left)

theorem idealModuleToUnit_mono {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Mono (IdealModule.idealModuleToUnit f) :=
  inferInstanceAs (Mono (kernel.ι
    (_root_.SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)))

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions
