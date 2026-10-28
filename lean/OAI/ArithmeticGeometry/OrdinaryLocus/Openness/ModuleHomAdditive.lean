import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf

/-! # Module Hom Additive -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomAdditive.Construction

noncomputable section

/-! Additive structure on the sheaf of local module homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def moduleHomLocalAddSubgroup {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens) :
    AddSubgroup ((Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ N.presheaf) where
  carrier := (ModuleHomSheaf.Construction.moduleHomSubfunctor M N).obj (.op U)
  zero_mem' := by
    intro V r
    change M.smul r ≫ 0 = 0 ≫ N.smul r
    exact Limits.comp_zero.trans Limits.zero_comp.symm
  add_mem' {q q'} hq hq' := by
    intro V r
    change M.smul r ≫ (q.app (.op V) + q'.app (.op V)) =
      (q.app (.op V) + q'.app (.op V)) ≫ N.smul r
    exact (Preadditive.comp_add _ _ _ _ _ _).trans
      ((congrArg₂ (fun a b ↦ a + b) (hq V r) (hq' V r)).trans
        (Preadditive.add_comp _ _ _ _ _ _).symm)
  neg_mem' {q} hq := by
    intro V r
    change M.smul r ≫ (-(q.app (.op V))) = (-(q.app (.op V))) ≫ N.smul r
    exact (Preadditive.comp_neg _ _).trans
      ((congrArg Neg.neg (hq V r)).trans (Preadditive.neg_comp _ _).symm)

def moduleHomAbPresheaf {X : Scheme.{u}} (M N : X.Modules) :
    X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (moduleHomLocalAddSubgroup M N U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := (ModuleHomSheaf.Construction.moduleHomSubfunctor M N).toFunctor.map f
      map_zero' := by apply Subtype.ext; rfl
      map_add' q q' := by apply Subtype.ext; rfl }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro q
    exact ConcreteCategory.congr_hom ((ModuleHomSheaf.Construction.moduleHomSubfunctor M N).toFunctor.map_id U) q
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro q
    exact ConcreteCategory.congr_hom ((ModuleHomSheaf.Construction.moduleHomSubfunctor M N).toFunctor.map_comp f g) q

def moduleHomAbSheaf {X : Scheme.{u}} (M N : X.Modules) :
    Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj := moduleHomAbPresheaf M N
  property := Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat)
    (ModuleHomSheaf.Construction.isSheaf_moduleHomSubfunctor M N)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomAdditive.Construction
