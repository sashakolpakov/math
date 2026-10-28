/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitScalar

/-! # Frame Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.SheafOfModules _root_.TopologicalSpace
universe u

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- A section on an ambient open, transported to the top open of its open subscheme. -/
noncomputable def affineOpenTopSection {Y : Scheme.{u}} (U : Y.affineOpens)
    (r : Γ(Y, U.1)) : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
  (U.1.ι.appIso ⊤).hom
    (Y.presheaf.map (eqToHom U.1.ι_image_top).op r)

/-- A top-open section of an open subscheme, transported back to the corresponding
ambient open. -/
noncomputable def affineOpenAmbientSection {Y : Scheme.{u}} (U : Y.affineOpens)
    (r : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) : Γ(Y, U.1) :=
  Y.presheaf.map (homOfLE U.1.ι_image_top.ge).op
    ((U.1.ι.appIso ⊤).inv r)

/-- Evaluating a top-open section after transport to its ambient affine open
agrees with evaluating it on the top open of the affine subscheme. -/
theorem sectionApp_affineOpenAmbientSection
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.affineOpens) (hU : f ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) :
    let htop : (⊤ : X.Opens) =
        f ⁻¹ᵁ (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) := by
      rw [U.1.ι_image_top, hU]
    X.presheaf.map (eqToHom htop).op
        (f.app (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))
          ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv r)) =
      X.presheaf.map (eqToHom hU.symm).op
        (f.app U.1 (affineOpenAmbientSection U r)) := by
  let htop : (⊤ : X.Opens) =
      f ⁻¹ᵁ (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) := by
    rw [U.1.ι_image_top, hU]
  change X.presheaf.map (eqToHom htop).op
      (f.app (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))
        ((U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv r)) =
    X.presheaf.map (eqToHom hU.symm).op
      (f.app U.1 (affineOpenAmbientSection U r))
  unfold affineOpenAmbientSection
  let i := (homOfLE U.1.ι_image_top.ge).op
  let r' := (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv r
  have hnat := ConcreteCategory.congr_hom
    (Scheme.Hom.naturality f i) r'
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  rw [hnat]
  let j := ((TopologicalSpace.Opens.map f.base).map i.unop).op
  have hmaps : X.presheaf.map j ≫
      X.presheaf.map (eqToHom hU.symm).op =
      X.presheaf.map (eqToHom htop).op := by
    rw [← X.presheaf.map_comp]
    congr 1
  change (X.presheaf.map (eqToHom htop).op).hom
      ((f.app (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))).hom r') =
    (X.presheaf.map (eqToHom hU.symm).op).hom
      ((X.presheaf.map j).hom
        ((f.app (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))).hom r'))
  have hmapsApply := ConcreteCategory.congr_hom hmaps
    ((f.app (U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))).hom r')
  simpa only [CommRingCat.comp_apply] using hmapsApply.symm

@[simp]
theorem affineOpenAmbientSection_add {Y : Scheme.{u}} (U : Y.affineOpens)
    (r s : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) :
    affineOpenAmbientSection U (r + s) =
      affineOpenAmbientSection U r + affineOpenAmbientSection U s := by
  unfold affineOpenAmbientSection
  rw [map_add, map_add]

@[simp]
theorem affineOpenAmbientSection_mul {Y : Scheme.{u}} (U : Y.affineOpens)
    (r s : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) :
    affineOpenAmbientSection U (r * s) =
      affineOpenAmbientSection U r * affineOpenAmbientSection U s := by
  unfold affineOpenAmbientSection
  rw [map_mul, map_mul]

@[simp]
theorem affineOpenAmbientSection_zero {Y : Scheme.{u}} (U : Y.affineOpens) :
    affineOpenAmbientSection U 0 = 0 := by
  unfold affineOpenAmbientSection
  rw [map_zero, map_zero]

@[simp]
theorem affineOpenTopSection_ambientSection {Y : Scheme.{u}}
    (U : Y.affineOpens) (r : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))) :
    affineOpenTopSection U (affineOpenAmbientSection U r) = r := by
  rw [affineOpenTopSection, affineOpenAmbientSection]
  change (U.1.ι.appIso ⊤).hom
      ((Y.presheaf.map (homOfLE U.1.ι_image_top.ge).op ≫
        Y.presheaf.map (eqToHom U.1.ι_image_top).op)
          ((U.1.ι.appIso ⊤).inv r)) = r
  have hmap : Y.presheaf.map
      (homOfLE U.1.ι_image_top.ge).op ≫
        Y.presheaf.map (eqToHom U.1.ι_image_top).op =
      𝟙 _ := by
    rw [← Y.presheaf.map_comp]
    simp
  rw [hmap]
  change (U.1.ι.appIso ⊤).hom ((U.1.ι.appIso ⊤).inv r) = r
  exact Iso.inv_hom_id_apply _ r

@[simp]
theorem affineOpenAmbientSection_topSection {Y : Scheme.{u}}
    (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    affineOpenAmbientSection U (affineOpenTopSection U r) = r := by
  rw [affineOpenAmbientSection, affineOpenTopSection]
  rw [Iso.hom_inv_id_apply]
  change (Y.presheaf.map (eqToHom U.1.ι_image_top).op ≫
    Y.presheaf.map (homOfLE U.1.ι_image_top.ge).op) r = r
  rw [← Y.presheaf.map_comp]
  simp

/-- Transporting an ambient affine section to the top open is the inverse of
the canonical restriction isomorphism. -/
theorem affineOpenTopSection_eq_topIso_inv {Y : Scheme.{u}}
    (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    affineOpenTopSection U r = U.1.topIso.inv.hom r := by
  unfold affineOpenTopSection
  rw [Scheme.Opens.ι_appIso]
  change (Y.presheaf.map (eqToHom U.1.ι_image_top).op).hom r =
    U.1.topIso.inv.hom r
  apply ConcreteCategory.congr_hom
  apply Y.presheaf.congr_map
  exact Subsingleton.elim _ _

noncomputable def affineOpenSectionsIso
    {Y : Scheme.{u}} (U : Y.affineOpens) :
    Γ(Y, U.1) ≅ Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
  Y.presheaf.mapIso (eqToIso U.1.ι_image_top).op ≪≫ U.1.ι.appIso ⊤

/-- A global module section, restricted to the top open of an affine open
subscheme. -/
noncomputable def localTrivializationRestriction {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) (m : Γ(M, (⊤ : X.Opens))) :
    Γ(M.restrict U.1.ι, (⊤ : U.1.toScheme.Opens)) :=
  (M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv
    (M.presheaf.map (eqToHom U.1.ι_image_top).op
      (M.presheaf.map (homOfLE le_top).op m))

@[simp]
theorem localTrivializationRestriction_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) (m n : Γ(M, (⊤ : X.Opens))) :
    localTrivializationRestriction M U (m + n) =
      localTrivializationRestriction M U m +
        localTrivializationRestriction M U n := by
  simp [localTrivializationRestriction, map_add]

@[simp]
theorem localTrivializationRestriction_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) : localTrivializationRestriction M U 0 = 0 := by
  simp [localTrivializationRestriction, map_zero]

/-- Transporting a scalar multiple of an ambient-open restriction to the top
open of the open subscheme transports the scalar as well. -/
theorem localTrivializationRestriction_smul_restrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (r : Γ(X, U.1)) (x : Γ(M, (⊤ : X.Opens))) :
    (M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)).inv
        (M.presheaf.map (eqToHom U.1.ι_image_top).op
          (r • M.presheaf.map U.1.leTop.op x)) =
      affineOpenTopSection U r • localTrivializationRestriction M U x := by
  rw [M.map_smul, Scheme.Modules.smul_restrictAppIso_inv_apply]
  rfl

/-- Restriction of a global module section to an affine open vanishes iff its
transport to the top open of the corresponding open subscheme vanishes. -/
theorem localTrivializationRestriction_eq_zero_iff
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens)
    (x : Γ(M, (⊤ : X.Opens))) :
    localTrivializationRestriction M U x = 0 ↔
      M.presheaf.map U.1.leTop.op x = 0 := by
  constructor
  · intro h
    let r := M.presheaf.map U.1.leTop.op x
    let e := M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)
    let p := M.presheaf.mapIso (eqToIso U.1.ι_image_top).op
    change e.inv
        (M.presheaf.map (eqToHom U.1.ι_image_top).op r) = 0 at h
    have h₁ := congrArg (fun q ↦ e.hom q) h
    rw [map_zero, e.inv_hom_id_apply] at h₁
    change r = 0
    apply (ConcreteCategory.bijective_of_isIso p.hom).1
    rw [map_zero]
    exact h₁
  · intro h
    let r := M.presheaf.map U.1.leTop.op x
    let e := M.restrictAppIso U.1.ι (⊤ : U.1.toScheme.Opens)
    let p := M.presheaf.mapIso (eqToIso U.1.ι_image_top).op
    change r = 0 at h
    change e.inv (p.hom r) = 0
    rw [h, map_zero, map_zero]

/-- Restricting a global section commutes with a morphism of scheme modules. -/
theorem localTrivializationRestriction_map
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.affineOpens) (m : Γ(M, (⊤ : X.Opens))) :
    localTrivializationRestriction N U (f.val.app (.op ⊤) m) =
      ((Scheme.Modules.restrictFunctor U.1.ι).map f).val.app (.op ⊤)
        (localTrivializationRestriction M U m) := by
  unfold localTrivializationRestriction
  have htop := PresheafOfModules.naturality_apply f.val
    (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op m
  have himage := PresheafOfModules.naturality_apply f.val
    (eqToHom U.1.ι_image_top).op
      (M.presheaf.map
        (homOfLE (le_top : U.1 ≤ (⊤ : X.Opens))).op m)
  erw [← htop, ← himage]
  rfl

/-- A restricted section, expressed in the trivial unit module. -/
noncomputable def localTrivializationTopSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (m : Γ(M, (⊤ : X.Opens))) :
    Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
  e.hom.val.app (.op ⊤) (localTrivializationRestriction M U m)

@[simp]
theorem localTrivializationTopSection_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (m n : Γ(M, (⊤ : X.Opens))) :
    localTrivializationTopSection M U e (m + n) =
      localTrivializationTopSection M U e m +
        localTrivializationTopSection M U e n := by
  unfold localTrivializationTopSection
  rw [localTrivializationRestriction_add]
  exact (e.hom.val.app (.op ⊤)).hom.map_add _ _

@[simp]
theorem localTrivializationTopSection_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme) :
    localTrivializationTopSection M U e 0 = 0 := by
  unfold localTrivializationTopSection
  rw [localTrivializationRestriction_zero]
  exact (e.hom.val.app (.op ⊤)).hom.map_zero

/-- The coefficient of a global module section in a chosen trivialization on an
affine open. -/
noncomputable def localTrivializationCoefficient {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (m : Γ(M, (⊤ : X.Opens))) : Γ(X, U.1) :=
  affineOpenAmbientSection U (localTrivializationTopSection M U e m)

@[simp]
theorem localTrivializationCoefficient_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme)
    (m n : Γ(M, (⊤ : X.Opens))) :
    localTrivializationCoefficient M U e (m + n) =
      localTrivializationCoefficient M U e m +
        localTrivializationCoefficient M U e n := by
  unfold localTrivializationCoefficient
  rw [localTrivializationTopSection_add, affineOpenAmbientSection_add]

@[simp]
theorem localTrivializationCoefficient_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ Invertible.Scheme.Modules.unitObj U.1.toScheme) :
    localTrivializationCoefficient M U e 0 = 0 := by
  unfold localTrivializationCoefficient
  rw [localTrivializationTopSection_zero, affineOpenAmbientSection_zero]

/-- A ring section, viewed as a module section through an over-site
trivialization. -/
noncomputable def overTrivializationSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) : Γ(M, U) :=
  e.inv.val.app (.op (Over.mk (𝟙 U))) r

/-- The coefficient of the module section constructed through a trivialization
is the original ring section. -/
theorem overTrivializationSection_coefficient {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) :
    e.hom.val.app (.op (Over.mk (𝟙 U)))
        (overTrivializationSection M U e r) = r := by
  have hcomp := congrArg (fun q => q.val.app (.op (Over.mk (𝟙 U))))
    e.inv_hom_id
  exact ConcreteCategory.congr_hom hcomp r

@[simp]
theorem overTrivializationSection_add {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r s : Γ(X, U)) :
    overTrivializationSection M U e (r + s) =
      overTrivializationSection M U e r + overTrivializationSection M U e s := by
  exact (e.inv.val.app (.op (Over.mk (𝟙 U)))).hom.map_add r s

@[simp]
theorem overTrivializationSection_smul {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (a b : Γ(X, U)) :
    a • overTrivializationSection M U e b =
      overTrivializationSection M U e (a * b) := by
  exact ((e.inv.val.app (.op (Over.mk (𝟙 U)))).hom.map_smul a b).symm

@[simp]
theorem overTrivializationSection_zero {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    overTrivializationSection M U e 0 = 0 := by
  exact (e.inv.val.app (.op (Over.mk (𝟙 U)))).hom.map_zero

/-- Constructing a section through a trivialization commutes with restriction
to a smaller open and the induced trivialization. -/
theorem overTrivializationSection_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U)) :
    M.presheaf.map (homOfLE hVU).op (overTrivializationSection M U e r) =
      overTrivializationSection M V
        (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE hVU)))
        (X.presheaf.map (homOfLE hVU).op r) := by
  unfold overTrivializationSection
  let VU : Over U := Over.mk (homOfLE hVU)
  let k : VU ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from VU
  have hnat := PresheafOfModules.naturality_apply e.inv.val k.op r
  change M.presheaf.map (homOfLE hVU).op
      (e.inv.val.app (.op (Over.mk (𝟙 U))) r) =
    e.inv.val.app (.op ((Over.map VU.hom).obj (Over.mk (𝟙 V))))
      (X.presheaf.map (homOfLE hVU).op r)
  change M.presheaf.map (Over.mkIdTerminal.from VU).left.op
      (e.inv.val.app (.op (Over.mk (𝟙 U))) r) =
    e.inv.val.app (.op VU)
      (X.presheaf.map (Over.mkIdTerminal.from VU).left.op r)
  exact hnat.symm

/-- Ring sections satisfying the scalar transition equation define the same
module section through the corresponding trivializations. -/
theorem overTrivializationSection_eq_of_transition
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r a b : Γ(X, U))
    (h : e.hom = g.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    (hab : a = b * r) :
    overTrivializationSection M U e a =
      overTrivializationSection M U g b := by
  have hright : e.hom.val.app (.op (Over.mk (𝟙 U)))
      (overTrivializationSection M U g b) = b * r := by
    have happ := congrArg
      (fun q => q.val.app (.op (Over.mk (𝟙 U)))) h
    have hx := ConcreteCategory.congr_hom happ
      (overTrivializationSection M U g b)
    change e.hom.val.app (.op (Over.mk (𝟙 U)))
        (g.inv.val.app (.op (Over.mk (𝟙 U))) b) =
      (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r).val.app
        (.op (Over.mk (𝟙 U)))
        (g.hom.val.app (.op (Over.mk (𝟙 U)))
          (g.inv.val.app (.op (Over.mk (𝟙 U))) b)) at hx
    have hg : g.hom.val.app (.op (Over.mk (𝟙 U)))
        (g.inv.val.app (.op (Over.mk (𝟙 U))) b) = b := by
      have hcomp := congrArg
        (fun q => q.val.app (.op (Over.mk (𝟙 U)))) g.inv_hom_id
      exact ConcreteCategory.congr_hom hcomp b
    rw [hg] at hx
    erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply
      X.ringCatSheaf U r (.op (Over.mk (𝟙 U))) b] at hx
    change e.hom.val.app (.op (Over.mk (𝟙 U)))
        (overTrivializationSection M U g b) =
      b * X.presheaf.map (𝟙 (.op U)) r at hx
    rw [X.presheaf.map_id, ConcreteCategory.id_apply] at hx
    exact hx
  have heq : e.hom.val.app (.op (Over.mk (𝟙 U)))
      (overTrivializationSection M U e a) =
      e.hom.val.app (.op (Over.mk (𝟙 U)))
        (overTrivializationSection M U g b) := by
    rw [overTrivializationSection_coefficient, hright, hab]
  have heq' := congrArg
    (fun x => e.inv.val.app (.op (Over.mk (𝟙 U))) x) heq
  have hcancel (x : (M.over U).val.obj (.op (Over.mk (𝟙 U)))) :
      e.inv.val.app (.op (Over.mk (𝟙 U)))
          (e.hom.val.app (.op (Over.mk (𝟙 U))) x) = x := by
    have hcomp := congrArg
      (fun q => q.val.app (.op (Over.mk (𝟙 U)))) e.hom_inv_id
    have hx := ConcreteCategory.congr_hom hcomp x
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at hx
    exact hx
  change (show (M.over U).val.obj (.op (Over.mk (𝟙 U))) from
      overTrivializationSection M U e a) =
    (show (M.over U).val.obj (.op (Over.mk (𝟙 U))) from
      overTrivializationSection M U g b)
  exact (hcancel (overTrivializationSection M U e a)).symm.trans
    (heq'.trans (hcancel (overTrivializationSection M U g b)))

/-- The coefficient of a global section in a trivialization on the over-site of an
open subset. -/
noncomputable def overTrivializationCoefficient {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(M, (⊤ : X.Opens))) : Γ(X, U) :=
  e.hom.val.app (.op (Over.mk (𝟙 U)))
    (M.presheaf.map (homOfLE le_top).op m)

/-- Equality of coefficients in an over-site trivialization detects equality
of the corresponding restricted module sections. -/
theorem restrict_eq_of_overTrivializationCoefficient_eq
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m n : Γ(M, (⊤ : X.Opens)))
    (h : overTrivializationCoefficient M U e m =
      overTrivializationCoefficient M U e n) :
    M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m =
      M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op n := by
  let T : Over U := Over.mk (𝟙 U)
  let mU := M.presheaf.map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m
  let nU := M.presheaf.map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op n
  change e.hom.val.app (.op T) mU = e.hom.val.app (.op T) nU at h
  have h' := congrArg (fun x => e.inv.val.app (.op T) x) h
  have hcancel (x : (M.over U).val.obj (.op T)) :
      e.inv.val.app (.op T) (e.hom.val.app (.op T) x) = x := by
    have hcomp := congrArg (fun q => q.val.app (.op T)) e.hom_inv_id
    have hx := ConcreteCategory.congr_hom hcomp x
    erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at hx
    exact hx
  change (show (M.over U).val.obj (.op T) from mU) =
    (show (M.over U).val.obj (.op T) from nU)
  exact (hcancel mU).symm.trans (h'.trans (hcancel nU))

/-- Expressing a scalar multiple in an over-site trivialization restricts the
scalar and multiplies the coefficient. -/
theorem overTrivializationCoefficient_smul {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (a : Γ(X, (⊤ : X.Opens))) (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M U e (a • m) =
      X.presheaf.map (homOfLE le_top).op a *
        overTrivializationCoefficient M U e m := by
  unfold overTrivializationCoefficient
  rw [M.map_smul]
  let T : Over U := Over.mk (𝟙 U)
  let c : (X.ringCatSheaf.over U).obj.obj (.op T) :=
    X.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op a
  let x : (M.over U).val.obj (.op T) :=
    M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m
  have h := (e.hom.val.app (.op T)).hom.map_smul c x
  change (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      e.hom.val.app (.op T) (c • x)) =
    c * (show (X.ringCatSheaf.over U).obj.obj (.op T) from
      e.hom.val.app (.op T) x) at h
  exact h

/-- Coefficients in a restricted over-site trivialization are restrictions of the
original coefficients. -/
theorem overTrivializationCoefficient_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M V
        (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
          (Over.mk (homOfLE hVU))) m =
      X.presheaf.map (homOfLE hVU).op
        (overTrivializationCoefficient M U e m) := by
  unfold overTrivializationCoefficient
  unfold Dual.SheafOfModules.restrictOverTrivialization
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  let VU : Over U := Over.mk (homOfLE hVU)
  change e.hom.val.app (.op VU)
      (M.presheaf.map (homOfLE (le_top : V ≤ (⊤ : X.Opens))).op m) =
    X.presheaf.map (homOfLE hVU).op
      (e.hom.val.app (.op (Over.mk (𝟙 U)))
        (M.presheaf.map (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m))
  let k : VU ⟶ Over.mk (𝟙 U) := Over.mkIdTerminal.from VU
  let mU := M.presheaf.map
    (homOfLE (le_top : U ≤ (⊤ : X.Opens))).op m
  have hnat := PresheafOfModules.naturality_apply e.hom.val k.op mU
  change e.hom.val.app (.op VU)
      ((M.over U).val.map k.op mU) =
    (X.ringCatSheaf.over U).obj.map k.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) mU) at hnat
  dsimp only [k] at hnat
  change e.hom.val.app (.op VU)
      (M.presheaf.map (Over.mkIdTerminal.from VU).left.op mU) =
    X.presheaf.map (Over.mkIdTerminal.from VU).left.op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) mU) at hnat
  rw [Over.mkIdTerminal_from_left] at hnat
  change e.hom.val.app (.op VU)
      (M.presheaf.map (homOfLE hVU).op mU) =
    X.presheaf.map (homOfLE hVU).op
      (e.hom.val.app (.op (Over.mk (𝟙 U))) mU) at hnat
  rw [← M.presheaf.map_comp_apply] at hnat
  exact hnat

/-- Coefficients transform by the same scalar as their over-site
trivializations. -/
theorem overTrivializationCoefficient_eq_mul_of_transition
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r)
    (m : Γ(M, (⊤ : X.Opens))) :
    overTrivializationCoefficient M U e m =
      overTrivializationCoefficient M U g m * r := by
  unfold overTrivializationCoefficient
  rw [h]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [Dual.SheafOfModules.overUnitScalarEnd_app_apply
    X.ringCatSheaf U r (.op (Over.mk (𝟙 U)))
    (g.hom.val.app (.op (Over.mk (𝟙 U)))
      (M.presheaf.map (homOfLE le_top).op m))]
  change _ * X.presheaf.map (𝟙 (.op U)) r = _ * r
  rw [X.presheaf.map_id]
  rw [ConcreteCategory.id_apply]

/-- An over-site trivialization gives the corresponding trivialization on the open
subscheme. -/
noncomputable def restrictTrivializationOfOverIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme :=
  (Scheme.Modules.overFunctorEquiv U).symm.app M ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
      U.sheafOfModulesEquivOverUnit X.ringCatSheaf

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections
