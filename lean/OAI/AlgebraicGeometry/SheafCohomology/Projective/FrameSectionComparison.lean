/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections

/-! # Frame Section Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSectionComparison

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.SheafOfModules _root_.TopologicalSpace
universe u

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem restrictTrivializationOfOverIso_hom_top_apply
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : ((M.restrict U.ι).val.obj (.op (⊤ : U.toScheme.Opens)))) :
    (FrameSections.restrictTrivializationOfOverIso M U e).hom.val.app (.op ⊤) x =
      e.hom.val.app
        (.op (U.overEquivalence.symm.functor.obj (⊤ : U.toScheme.Opens)))
        (((Scheme.Modules.overFunctorEquiv U).inv.app M).val.app (.op ⊤) x) := by
  unfold FrameSections.restrictTrivializationOfOverIso
  simp only [Iso.trans_hom]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]

theorem affineOpenTopSection_eq_overMap_terminal
    {X : Scheme.{u}} (U : X.affineOpens) (r : Γ(X, U.1)) :
    let V := U.1.overEquivalence.symm.functor.obj
      (⊤ : U.1.toScheme.Opens)
    let k : V ⟶ Over.mk (𝟙 U.1) := Over.mkIdTerminal.from V
    FrameSections.affineOpenTopSection U r =
      (X.ringCatSheaf.over U.1).obj.map k.op r := by
  dsimp only
  unfold FrameSections.affineOpenTopSection
  rw [U.1.ι_appIso]
  change X.presheaf.map (eqToHom U.1.ι_image_top).op r =
    X.presheaf.map
      (Over.mkIdTerminal.from
        (U.1.overEquivalence.symm.functor.obj
          (⊤ : U.1.toScheme.Opens))).left.op r
  congr 2
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

theorem localTrivializationRestriction_eq_overMap_terminal
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (m : Γ(M, (⊤ : X.Opens))) :
    let V := U.1.overEquivalence.symm.functor.obj
      (⊤ : U.1.toScheme.Opens)
    let k : V ⟶ Over.mk (𝟙 U.1) := Over.mkIdTerminal.from V
    ((Scheme.Modules.overFunctorEquiv U.1).inv.app M).val.app (.op ⊤)
        (FrameSections.localTrivializationRestriction M U m) =
      (M.over U.1).val.map k.op
        (M.presheaf.map (homOfLE le_top).op m) := by
  dsimp only
  unfold FrameSections.localTrivializationRestriction
  change M.presheaf.map (eqToHom U.1.ι_image_top).op
      (M.presheaf.map (homOfLE le_top).op m) =
    M.presheaf.map
      (Over.mkIdTerminal.from
        (U.1.overEquivalence.symm.functor.obj
          (⊤ : U.1.toScheme.Opens))).left.op
      (M.presheaf.map (homOfLE le_top).op m)
  congr 2
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

theorem overTrivializationCoefficient_eq_local_of_overIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (m : Γ(M, (⊤ : X.Opens))) :
    FrameSections.overTrivializationCoefficient M U.1 e m =
      FrameSections.localTrivializationCoefficient M U
        (FrameSections.restrictTrivializationOfOverIso M U.1 e) m := by
  rw [← FrameSections.affineOpenAmbientSection_topSection U
    (FrameSections.overTrivializationCoefficient M U.1 e m)]
  unfold FrameSections.localTrivializationCoefficient
  congr 1
  unfold FrameSections.localTrivializationTopSection FrameSections.overTrivializationCoefficient
  erw [restrictTrivializationOfOverIso_hom_top_apply M U.1 e
    (FrameSections.localTrivializationRestriction M U m)]
  rw [localTrivializationRestriction_eq_overMap_terminal]
  erw [affineOpenTopSection_eq_overMap_terminal U
    (e.hom.val.app (.op (Over.mk (𝟙 U.1)))
      (M.presheaf.map (homOfLE le_top).op m))]
  let V := U.1.overEquivalence.symm.functor.obj
    (⊤ : U.1.toScheme.Opens)
  let k : V ⟶ Over.mk (𝟙 U.1) := Over.mkIdTerminal.from V
  let mU := M.presheaf.map
    (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op m
  have hnat := PresheafOfModules.naturality_apply e.hom.val k.op mU
  exact hnat.symm

/-- If a morphism from the structure module is multiplication by `r` in an over-site
trivialization, then the affine local coordinate of its value at `1` is `r`. -/
theorem localTrivializationTopSection_unitHom_apply_one
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (f : Invertible.Scheme.Modules.unitObj X ⟶ M)
    (e : M.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (r : Γ(X, U.1))
    (h : f.over U.1 ≫ e.hom =
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U.1 r) :
    FrameSections.localTrivializationTopSection M U
        (FrameSections.restrictTrivializationOfOverIso M U.1 e)
        (f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)) =
      FrameSections.affineOpenTopSection U r := by
  let m := f.val.app (.op ⊤) (show X.presheaf.obj (.op ⊤) from 1)
  have hcoeffOver : FrameSections.overTrivializationCoefficient M U.1 e m = r := by
    unfold FrameSections.overTrivializationCoefficient
    have hnat := PresheafOfModules.naturality_apply f.val
      (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op
      (show X.presheaf.obj (.op ⊤) from 1)
    let oneU : (Invertible.Scheme.Modules.unitObj X).val.obj (.op U.1) :=
      show X.presheaf.obj (.op U.1) from 1
    have honeRestrict :
        (Invertible.Scheme.Modules.unitObj X).presheaf.map
            (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op
            (show X.presheaf.obj (.op ⊤) from 1) = oneU := by
      change X.presheaf.map (homOfLE le_top).op 1 = 1
      exact map_one _
    have hnat' : f.val.app (.op U.1) oneU =
        M.presheaf.map (homOfLE le_top).op m := by
      exact (congrArg (fun a ↦ f.val.app (.op U.1) a)
        honeRestrict.symm).trans hnat
    have happ := congrArg
      (fun q ↦ q.val.app (.op (Over.mk (𝟙 U.1)))) h
    let oneRing : X.ringCatSheaf.obj.obj (.op U.1) := by
      change X.presheaf.obj (.op U.1)
      exact 1
    have hone := ConcreteCategory.congr_hom happ
      oneRing
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at hone
    erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply] at hone
    have hover :
        (f.over U.1).val.app (.op (Over.mk (𝟙 U.1))) oneRing =
          f.val.app (.op U.1) oneU := by
      rfl
    let rRing : X.ringCatSheaf.obj.obj (.op U.1) := by
      change X.presheaf.obj (.op U.1)
      exact r
    have hrOver : X.ringCatSheaf.obj.map
        (Opposite.unop (.op (Over.mk (𝟙 U.1)))).hom.op r = rRing := by
      rw [Subsingleton.elim
        (Opposite.unop (.op (Over.mk (𝟙 U.1)))).hom.op
        (𝟙 (Opposite.op U.1))]
      have hr' := ConcreteCategory.congr_hom
        (X.ringCatSheaf.obj.map_id (.op U.1)) r
      exact hr'.trans rfl
    have hone' : e.hom.val.app (.op (Over.mk (𝟙 U.1)))
        (f.val.app (.op U.1) oneU) = r := by
      rw [hrOver] at hone
      have honeMul : oneRing * rRing = rRing := by
        change (1 : X.presheaf.obj (.op U.1)) * r = r
        exact one_mul r
      change e.hom.val.app (.op (Over.mk (𝟙 U.1)))
          ((f.over U.1).val.app (.op (Over.mk (𝟙 U.1))) oneRing) =
        oneRing * rRing at hone
      rw [honeMul] at hone
      have hlocal := (congrArg
        (fun a ↦ e.hom.val.app (.op (Over.mk (𝟙 U.1))) a)
        hover.symm).trans hone
      exact hlocal
    exact (congrArg (fun a ↦ e.hom.val.app (.op (Over.mk (𝟙 U.1))) a)
      hnat'.symm).trans hone'
  have hcoeffLocal :
      FrameSections.localTrivializationCoefficient M U
          (FrameSections.restrictTrivializationOfOverIso M U.1 e) m = r :=
    (overTrivializationCoefficient_eq_local_of_overIso M U e m).symm.trans hcoeffOver
  have htop := congrArg (FrameSections.affineOpenTopSection U) hcoeffLocal
  exact (FrameSections.affineOpenTopSection_ambientSection U _).symm.trans htop

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSectionComparison
