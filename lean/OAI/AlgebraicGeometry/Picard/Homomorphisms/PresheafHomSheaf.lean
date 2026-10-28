import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSections

/-! # Presheaf Hom Sheaf -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafHomSheaf

noncomputable section

/-! Local linear maps from a module presheaf to a module sheaf form a module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (M : X.PresheafOfModules) (N : X.Modules)

local instance presheafHomSheafLocal1 (U : X.Opens) : Module Γ(X, U) (M.obj (.op U)) := (M.obj (.op U)).isModule

def IsLinearPresheafLocalHom {U : X.Opens}
    (a : (presheafHom M.presheaf N.presheaf).obj (.op U)) : Prop :=
  ∀ (V : Over U) (r : Γ(X, V.left)) (s : M.obj (.op V.left)),
    a.app (.op V) (r • s) = r • (show Γ(N, V.left) from a.app (.op V) s)

instance localPresheafHomAddCommGroup (U : X.Opensᵒᵖ) :
    AddCommGroup ((presheafHom M.presheaf N.presheaf).obj U) :=
  inferInstanceAs (AddCommGroup
    (((Over.forget U.unop).op ⋙ M.presheaf) ⟶ ((Over.forget U.unop).op ⋙ N.presheaf)))

instance localPresheafHomModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((presheafHom M.presheaf N.presheaf).obj U) :=
  Module.compHom (((Over.forget U.unop).op ⋙ M.presheaf) ⟶ ((Over.forget U.unop).op ⋙ N.presheaf))
    (ModuleHomSections.Construction.localSectionScalarEnd N U.unop)

def presheafLinearHomSubmodule (U : X.Opensᵒᵖ) :
    Submodule (X.ringCatSheaf.obj.obj U) ((presheafHom M.presheaf N.presheaf).obj U) where
  carrier := {a | IsLinearPresheafLocalHom M N a}
  zero_mem' := by
    intro V r s
    change (0 : Γ(N, V.left)) = r • 0
    rw [smul_zero]
  add_mem' {a b} ha hb := by
    intro V r s
    change (show Γ(N, V.left) from a.app (.op V) (r • s)) +
        (show Γ(N, V.left) from b.app (.op V) (r • s)) =
      r • ((show Γ(N, V.left) from a.app (.op V) s) + (show Γ(N, V.left) from b.app (.op V) s))
    rw [ha, hb, smul_add]
  smul_mem' r a ha := by
    intro V t s
    change X.presheaf.map V.hom.op r • (show Γ(N, V.left) from a.app (.op V) (t • s)) =
      t • (X.presheaf.map V.hom.op r • (show Γ(N, V.left) from a.app (.op V) s))
    rw [ha]
    exact smul_comm _ _ _

def presheafLinearHomSubfunctor : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := presheafLinearHomSubmodule M N U
  map {U V} f a ha := by
    intro W r s
    exact ha ((Over.map f.unop).obj W) r s

theorem presheafLinearHomSubfunctor_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (presheafLinearHomSubfunctor M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply ((presheafLinearHomSubfunctor M N).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type _ _).mp (N.isSheaf.hom M.presheaf))).mpr
  intro U a ha V r s
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨W, i, hi, hxW⟩ := ha x ((leOfHom V.hom) hx)
  let Z := V.left ⊓ W
  let z : Over U.unop := Over.mk (homOfLE (show Z ≤ U.unop from inf_le_left.trans (leOfHom V.hom)))
  let j : z ⟶ V := Over.homMk (homOfLE (show Z ≤ V.left from inf_le_left))
  have hn (t : M.obj (.op V.left)) := ConcreteCategory.congr_hom (a.naturality j.op) t
  change ∀ t : M.obj (.op V.left),
    a.app (.op z) (M.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op t) =
      N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op (a.app (.op V) t) at hn
  have hl := hi (Over.mk (homOfLE (show Z ≤ W from inf_le_right)))
    (X.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op r)
    (M.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op s)
  refine ⟨Z, inf_le_left, ⟨hx, hxW⟩, ?_⟩
  change N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op (a.app (.op V) (r • s)) =
    N.presheaf.map (homOfLE (show Z ≤ V.left from inf_le_left)).op
      (r • (show Γ(N, V.left) from a.app (.op V) s))
  have hsm := N.val.map_smul (homOfLE (show Z ≤ V.left from inf_le_left)).op r (a.app (.op V) s)
  erw [hsm, ← hn (r • s), ← hn s, M.map_smul]
  exact hl

instance presheafLinearHomSectionAddCommGroup (U : X.Opensᵒᵖ) :
    AddCommGroup ((presheafLinearHomSubfunctor M N).toFunctor.obj U) :=
  inferInstanceAs (AddCommGroup (presheafLinearHomSubmodule M N U))

instance presheafLinearHomSectionModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((presheafLinearHomSubfunctor M N).toFunctor.obj U) :=
  inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (presheafLinearHomSubmodule M N U))

def presheafLinearHomAbPresheaf : TopCat.Presheaf Ab X where
  obj U := AddCommGrpCat.of ((presheafLinearHomSubfunctor M N).toFunctor.obj U)
  map f := AddCommGrpCat.ofHom
    { toFun := (presheafLinearHomSubfunctor M N).toFunctor.map f
      map_zero' := Subtype.ext rfl
      map_add' _ _ := Subtype.ext rfl }
  map_id U := by
    ext a
    exact (presheafLinearHomSubfunctor M N).toFunctor.map_id_apply U a
  map_comp f g := by
    ext a
    exact (presheafLinearHomSubfunctor M N).toFunctor.map_comp_apply f g a

instance presheafLinearHomAbModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((presheafLinearHomAbPresheaf M N).obj U) :=
  presheafLinearHomSectionModule M N U

theorem presheafLinearHomAb_map_smul {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (r : X.ringCatSheaf.obj.obj U) (a : (presheafLinearHomAbPresheaf M N).obj U) :
    (presheafLinearHomAbPresheaf M N).map f (r • a) =
      X.ringCatSheaf.obj.map f r • (presheafLinearHomAbPresheaf M N).map f a := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro s
  change X.presheaf.map (W.unop.hom ≫ f.unop).op r •
      (show Γ(N, W.unop.left) from a.val.app (.op ((Over.map f.unop).obj W.unop)) s) =
    X.presheaf.map W.unop.hom.op (X.presheaf.map f r) •
      (show Γ(N, W.unop.left) from a.val.app (.op ((Over.map f.unop).obj W.unop)) s)
  rw [op_comp, Functor.map_comp_apply]
  rfl

def presheafInternalHom : X.Modules where
  val := PresheafOfModules.ofPresheaf (presheafLinearHomAbPresheaf M N)
    (fun {_ _} f r a => presheafLinearHomAb_map_smul M N f r a)
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp _ (presheafLinearHomAbPresheaf M N) (forget Ab)
    (presheafLinearHomSubfunctor_isSheaf M N)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PresheafHomSheaf
