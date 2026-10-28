/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # Linear Hom -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LinearHom

noncomputable section

/-! The sheaf of local module-linear morphisms between two actual modules. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})

def ambientLinearHom (M N : _root_.SheafOfModules R) :=
  CategoryTheory.sheafHom ((_root_.SheafOfModules.toSheaf R).obj M)
    ((_root_.SheafOfModules.toSheaf R).obj N)

def linearHomToAmbient (M N : _root_.SheafOfModules R) (U : C) :
    (M.over U ⟶ N.over U) → (ambientLinearHom R M N).obj.obj (.op U) :=
  fun f => (_root_.SheafOfModules.toSheaf (R.over U)).map f

def linearHomRestrict (M N : _root_.SheafOfModules R) {U V : Cᵒᵖ}
    (f : U ⟶ V) (a : M.over U.unop ⟶ N.over U.unop) :
    M.over V.unop ⟶ N.over V.unop :=
  (_root_.SheafOfModules.overFunctorMap R f.unop).inv.app M ≫
    (_root_.SheafOfModules.overMap R f.unop).map a ≫
    (_root_.SheafOfModules.overFunctorMap R f.unop).hom.app N

theorem ambientLinearHom_map_linearHomToAmbient (M N : _root_.SheafOfModules R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (a : M.over U.unop ⟶ N.over U.unop) :
    (ambientLinearHom R M N).obj.map f (linearHomToAmbient R M N U.unop a) =
    linearHomToAmbient R M N V.unop (linearHomRestrict R M N f a) := rfl

/-- The module-linear local functionals, viewed as a subpresheaf of the additive
internal Hom. -/
noncomputable def linearHomSubfunctor (M N : _root_.SheafOfModules R) :
    Subfunctor (ambientLinearHom R M N).obj where
  obj U := Set.range (linearHomToAmbient R M N U.unop)
  map f _ := by
    rintro ⟨α, rfl⟩
    exact ⟨linearHomRestrict R M N f α, ambientLinearHom_map_linearHomToAmbient R M N f α⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- If a section `s` of the additive internal Hom over `U` restricts to module-linear
functionals along a `J`-covering sieve, then `s` is itself module-linear. This is the
linearity-descent step in the sheaf condition for the module-linear dual. -/
theorem linearHomSubfunctor_hom_app_smul (M N : _root_.SheafOfModules R) {U : Cᵒᵖ}
    (s : (ambientLinearHom R M N).obj.obj U)
    (hs : (linearHomSubfunctor R M N).sieveOfSection s ∈ J U.unop)
    (V : (Over U.unop)ᵒᵖ) (r : (R.over U.unop).obj.obj V)
    (m : (M.over U.unop).val.obj V) :
    s.hom.app V (r • m) =
      r • (show (N.over U.unop).val.obj V from
        s.hom.app V m) := by
  let T : Sieve V.unop :=
    (Sieve.overEquiv V.unop).symm
      (Sieve.pullback (V.unop.hom) ((linearHomSubfunctor R M N).sieveOfSection s))
  have hT : T ∈ (J.over U.unop) V.unop :=
    J.overEquiv_symm_mem_over V.unop _ (J.pullback_stable (V.unop.hom) hs)
  apply (N.over U.unop).isSheaf.isSeparated
    V.unop T hT
  intro W i hi
  erw [← CategoryTheory.congr_fun (s.hom.naturality i.op) (r • m)]
  change s.hom.app (op W)
      ((M.over U.unop).val.map i.op (r • m)) =
    (N.over U.unop).val.map i.op
      (r • (show (N.over U.unop).val.obj V from
        s.hom.app V m))
  rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul]
  erw [← CategoryTheory.congr_fun (s.hom.naturality i.op) m]
  have hi' :
      (Sieve.pullback (V.unop.hom)
        ((linearHomSubfunctor R M N).sieveOfSection s)) i.left :=
    (Sieve.overEquiv_symm_iff _ i).mp hi
  change (ambientLinearHom R M N).obj.map (i.left ≫ V.unop.hom).op s ∈
    (linearHomSubfunctor R M N).obj (op W.left) at hi'
  rcases hi' with ⟨β, hβ⟩
  change s.hom.app (op W)
      ((R.over U.unop).obj.map i.op r • (M.over U.unop).val.map i.op m) =
    (R.over U.unop).obj.map i.op r •
      (show (N.over U.unop).val.obj (op W) from
        s.hom.app (op W) ((M.over U.unop).val.map i.op m))
  rw [Over.w i] at hβ
  have hβ_app := congr_arg
    (fun q => q.hom.app (op (Over.mk (𝟙 W.left)))) hβ
  let r' : (R.over W.left).obj.obj (op (Over.mk (𝟙 W.left))) :=
    (R.over U.unop).obj.map i.op r
  let m' : (M.over W.left).val.obj (op (Over.mk (𝟙 W.left))) :=
    (M.over U.unop).val.map i.op m
  have hβ_smul := CategoryTheory.congr_fun hβ_app (r' • m')
  have hβ_m := CategoryTheory.congr_fun hβ_app m'
  have hleft_smul :
      (linearHomToAmbient R M N W.left β).hom.app (op (Over.mk (𝟙 W.left)))
          (r' • m') =
        β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') := rfl
  have hleft_m :
      (linearHomToAmbient R M N W.left β).hom.app (op (Over.mk (𝟙 W.left))) m' =
        β.val.app (op (Over.mk (𝟙 W.left))) m' := rfl
  have hright_smul :
      (((ambientLinearHom R M N).obj.map W.hom.op s).hom.app
          (op (Over.mk (𝟙 W.left)))) (r' • m') =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') := rfl
  have hright_m :
      (((ambientLinearHom R M N).obj.map W.hom.op s).hom.app
          (op (Over.mk (𝟙 W.left)))) m' =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' := rfl
  have hβ_canon_smul :
      β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') :=
    hleft_smul.symm.trans (hβ_smul.trans hright_smul)
  have hβ_canon_m :
      β.val.app (op (Over.mk (𝟙 W.left))) m' =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' :=
    hleft_m.symm.trans (hβ_m.trans hright_m)
  let e : (Over.map W.hom).obj (Over.mk (𝟙 W.left)) ≅ W :=
    Over.isoMk (Iso.refl _) (by rfl)
  have hs_canon_smul :
      s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') = s.hom.app (op W) (r' • m') := by
    have h := CategoryTheory.congr_fun (s.hom.naturality e.hom.op) (r' • m')
    dsimp [e] at h
    change s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).obj.map (𝟙 W.left).op
          (r' • m')) =
      ((_root_.SheafOfModules.toSheaf R).obj
          N).obj.map (𝟙 W.left).op
        (s.hom.app (op W) (r' • m')) at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).obj.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        N).obj.map_id] at h
    simpa using h
  have hs_canon_m :
      s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' =
        s.hom.app (op W) m' := by
    have h := CategoryTheory.congr_fun (s.hom.naturality e.hom.op) m'
    dsimp [e] at h
    change s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).obj.map (𝟙 W.left).op m') =
      ((_root_.SheafOfModules.toSheaf R).obj
          N).obj.map (𝟙 W.left).op
        (s.hom.app (op W) m') at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).obj.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        N).obj.map_id] at h
    simpa using h
  change s.hom.app (op W) (r' • m') =
    r' • (show (N.over W.left).val.obj
      (op (Over.mk (𝟙 W.left))) from s.hom.app (op W) m')
  rw [← hs_canon_smul, ← hs_canon_m, ← hβ_canon_smul, ← hβ_canon_m]
  exact (β.val.app (op (Over.mk (𝟙 W.left)))).hom.map_smul r' m'

set_option backward.isDefEq.respectTransparency.types false in
/-- Module-linearity of a local functional descends along covering sieves. -/
theorem linearHomSubfunctor_isSheaf (M N : _root_.SheafOfModules R) :
    Presieve.IsSheaf J (linearHomSubfunctor R M N).toFunctor := by
  apply ((linearHomSubfunctor R M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type J (ambientLinearHom R M N).obj).mp
      (ambientLinearHom R M N).property)).2
  intro U s hs
  let α : M.over U.unop ⟶ N.over U.unop :=
    { val := PresheafOfModules.homMk s.hom (linearHomSubfunctor_hom_app_smul R M N s hs) }
  exact ⟨α, rfl⟩

/-- Local module-linear morphisms form an actual sheaf of types. -/
def linearHomSheaf (M N : _root_.SheafOfModules R) : Sheaf J (Type u) where
  obj := (linearHomSubfunctor R M N).toFunctor
  property := (isSheaf_iff_isSheaf_of_type J _).mpr (linearHomSubfunctor_isSheaf R M N)

def linearHomForgetSections (M N : _root_.SheafOfModules R)
    (s : (linearHomSheaf R M N).obj.sections) :
    (ambientLinearHom R M N).obj.sections :=
  ⟨fun U => (s.val U).val, fun {_ _} f => congrArg Subtype.val (s.property f)⟩

/-- A compatible family of local module-linear maps defines a global module map. -/
def moduleHomOfSections (M N : _root_.SheafOfModules R)
    (s : (linearHomSheaf R M N).obj.sections) : M ⟶ N := by
  let E := sheafHomSectionsEquiv ((_root_.SheafOfModules.toSheaf R).obj M)
    ((_root_.SheafOfModules.toSheaf R).obj N)
  let t := linearHomForgetSections R M N s
  let a := E t
  refine { val := PresheafOfModules.homMk a.hom ?_ }
  intro U r x
  have hs := congrArg
    (fun q => (q.val U).hom.app (.op (Over.mk (𝟙 U.unop)))) (E.symm_apply_apply t)
  change a.hom.app U = (s.val U).val.hom.app (.op (Over.mk (𝟙 U.unop))) at hs
  obtain ⟨b, hb⟩ := (s.val U).property
  have he := congrArg
    (fun q => q.hom.app (.op (Over.mk (𝟙 U.unop)))) hb
  rw [hs, ← he]
  exact (b.val.app (.op (Over.mk (𝟙 U.unop)))).hom.map_smul r x

theorem moduleHomOfSections_over (M N : _root_.SheafOfModules R)
    (s : (linearHomSheaf R M N).obj.sections) (U : C) :
    linearHomToAmbient R M N U ((moduleHomOfSections R M N s).over U) =
      (s.val (.op U)).val := by
  let E := sheafHomSectionsEquiv ((_root_.SheafOfModules.toSheaf R).obj M)
    ((_root_.SheafOfModules.toSheaf R).obj N)
  let t := linearHomForgetSections R M N s
  have h := congrArg (fun q => q.val (.op U)) (E.symm_apply_apply t)
  exact h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LinearHom
