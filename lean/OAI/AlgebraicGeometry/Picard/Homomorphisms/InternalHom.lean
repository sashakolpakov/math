import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomSections

/-! # Internal Hom -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHom

noncomputable section

/-! The internal Hom as an actual sheaf of modules on a scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

local instance (U : X.Opensᵒᵖ) :
    AddCommGroup ((ModuleHomSheaf.Construction.linearHomSubfunctor M N).toFunctor.obj U) :=
  ModuleHomSections.Construction.linearHomSectionAddCommGroup M N U.unop

local instance (U : X.Opensᵒᵖ) :
    AddCommGroup ((presheafHom M.presheaf N.presheaf).obj U) :=
  ModuleHomSections.Construction.localAdditiveHomAddCommGroup M N U.unop

local instance (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((presheafHom M.presheaf N.presheaf).obj U) :=
  ModuleHomSections.Construction.localAdditiveHomModule M N U.unop

def linearHomAbPresheaf : TopCat.Presheaf Ab X where
  obj U := AddCommGrpCat.of ((ModuleHomSheaf.Construction.linearHomSubfunctor M N).toFunctor.obj U)
  map f := AddCommGrpCat.ofHom
    { toFun := (ModuleHomSheaf.Construction.linearHomSubfunctor M N).toFunctor.map f
      map_zero' := Subtype.ext rfl
      map_add' _ _ := Subtype.ext rfl }
  map_id U := by
    ext a
    exact (ModuleHomSheaf.Construction.linearHomSubfunctor M N).toFunctor.map_id_apply U a
  map_comp f g := by
    ext a
    exact (ModuleHomSheaf.Construction.linearHomSubfunctor M N).toFunctor.map_comp_apply f g a

instance linearHomAbPresheafModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((linearHomAbPresheaf M N).obj U) :=
  ModuleHomSections.Construction.linearHomSectionModule M N U.unop

theorem linearHomAbPresheaf_map_smul {U V : X.Opensᵒᵖ} (f : U ⟶ V)
    (r : X.ringCatSheaf.obj.obj U) (a : (linearHomAbPresheaf M N).obj U) :
    (linearHomAbPresheaf M N).map f (r • a) =
      X.ringCatSheaf.obj.map f r • (linearHomAbPresheaf M N).map f a := by
  apply Subtype.ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.ext
  intro s
  change X.presheaf.map (W.unop.hom ≫ f.unop).op r •
      (show Γ(N, W.unop.left) from a.val.app (.op ((Over.map f.unop).obj W.unop)) s) =
    X.presheaf.map W.unop.hom.op (X.presheaf.map f r) •
      (show Γ(N, W.unop.left) from a.val.app (.op ((Over.map f.unop).obj W.unop)) s)
  have hr : X.presheaf.map W.unop.hom.op (X.presheaf.map f r) =
      X.presheaf.map (W.unop.hom ≫ f.unop).op r := by
    rw [op_comp, Functor.map_comp_apply]
    rfl
  exact congrArg (fun c : Γ(X, W.unop.left) =>
    c • (show Γ(N, W.unop.left) from a.val.app (.op ((Over.map f.unop).obj W.unop)) s)) hr.symm

theorem linearHomAbPresheaf_isSheaf : (linearHomAbPresheaf M N).IsSheaf :=
  Presheaf.isSheaf_of_isSheaf_comp _ (linearHomAbPresheaf M N) (forget Ab)
    (ModuleHomSheaf.Construction.linearHomSubfunctor_isSheaf M N)

/-- Internal Hom with sections equal to linear maps on the restricted open. -/
def moduleInternalHom : X.Modules where
  val := PresheafOfModules.ofPresheaf (linearHomAbPresheaf M N)
    (fun {_ _} f r a => linearHomAbPresheaf_map_smul M N f r a)
  isSheaf := linearHomAbPresheaf_isSheaf M N

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHom
