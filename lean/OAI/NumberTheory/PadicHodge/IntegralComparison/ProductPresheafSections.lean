import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Product Presheaf Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProductPresheafSections

noncomputable section

/-!
# IntegralComparison: constant-source sections of a product presheaf

Evaluation along the diagonal recovers the original section on the frame.
The inverse pulls it back along the first projection.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z t

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type w} [Category.{z} D] (F : C) (P : Cᵒᵖ ⥤ D) (M : D)

abbrev productPresheaf : Cᵒᵖ ⥤ D := (prod.functor.obj F).op ⋙ P

omit [HasBinaryProducts C] in
theorem map_comp_op {U V W : C} (g : U ⟶ V) (h : V ⟶ W) :
    P.map h.op ≫ P.map g.op = P.map (g ≫ h).op :=
  (P.map_comp h.op g.op).symm

omit [HasBinaryProducts C] in
theorem pull_comp {U V W : C} (a : M ⟶ P.obj (op W)) (g : U ⟶ V) (h : V ⟶ W) :
    (a ≫ P.map h.op) ≫ P.map g.op = a ≫ P.map (g ≫ h).op :=
  (Category.assoc _ _ _).trans (congrArg (fun t => a ≫ t) (map_comp_op P g h))

def fromFrame (g : M ⟶ P.obj (op F)) : (Functor.const Cᵒᵖ).obj M ⟶ productPresheaf F P where
  app U := g ≫ P.map (prod.fst : F ⨯ U.unop ⟶ F).op
  naturality U V α := by
    have h := (prod.map_fst (𝟙 F) α.unop).trans (Category.comp_id _)
    exact (Category.id_comp _).trans
      ((congrArg (fun t => g ≫ P.map t.op) h).symm.trans
        (pull_comp P M g (prod.map (𝟙 F) α.unop) prod.fst).symm)

def toFrame (a : (Functor.const Cᵒᵖ).obj M ⟶ productPresheaf F P) : M ⟶ P.obj (op F) :=
  a.app (op F) ≫ P.map (prod.lift (𝟙 F) (𝟙 F)).op

theorem toFrame_fromFrame (g : M ⟶ P.obj (op F)) :
    toFrame F P M (fromFrame F P M g) = g := by
  exact (pull_comp P M g (prod.lift (𝟙 F) (𝟙 F)) prod.fst).trans
    ((congrArg (fun t => g ≫ P.map t.op) (prod.lift_fst (𝟙 F) (𝟙 F))).trans
      ((congrArg (fun t => g ≫ t) (P.map_id (op F))).trans (Category.comp_id g)))

theorem fromFrame_toFrame (a : (Functor.const Cᵒᵖ).obj M ⟶ productPresheaf F P) :
    fromFrame F P M (toFrame F P M a) = a := by
  apply NatTrans.ext
  funext U
  let aF : M ⟶ P.obj (op (F ⨯ F)) := a.app (op F)
  let aU : M ⟶ P.obj (op (F ⨯ U.unop)) := a.app U
  let aP : M ⟶ P.obj (op (F ⨯ (F ⨯ U.unop))) := a.app (op (F ⨯ U.unop))
  let d : F ⨯ U.unop ⟶ F ⨯ (F ⨯ U.unop) := prod.lift prod.fst (𝟙 _)
  have hf : aP = aF ≫ P.map (prod.map (𝟙 F) prod.fst).op :=
    (Category.id_comp aP).symm.trans (a.naturality (prod.fst : F ⨯ U.unop ⟶ F).op)
  have hs : aP = aU ≫ P.map (prod.map (𝟙 F) prod.snd).op :=
    (Category.id_comp aP).symm.trans (a.naturality (prod.snd : F ⨯ U.unop ⟶ U.unop).op)
  have hfirst : d ≫ prod.map (𝟙 F) (prod.fst : F ⨯ U.unop ⟶ F) =
      prod.fst ≫ prod.lift (𝟙 F) (𝟙 F) := by
    apply prod.hom_ext <;> simp [d]
  have hsecond : d ≫ prod.map (𝟙 F) (prod.snd : F ⨯ U.unop ⟶ U.unop) = 𝟙 _ := by
    apply prod.hom_ext <;> simp [d]
  exact (pull_comp P M aF prod.fst (prod.lift (𝟙 F) (𝟙 F))).trans
    ((congrArg (fun t => aF ≫ P.map t.op) hfirst).symm.trans
      ((pull_comp P M aF d (prod.map (𝟙 F) prod.fst)).symm.trans
        ((congrArg (fun t => t ≫ P.map d.op) (hf.symm.trans hs)).trans
          ((pull_comp P M aU d (prod.map (𝟙 F) prod.snd)).trans
            ((congrArg (fun t => aU ≫ P.map t.op) hsecond).trans
              ((congrArg (fun t => aU ≫ t) (P.map_id (op (F ⨯ U.unop)))).trans
                (Category.comp_id aU)))))))

def homEquiv : ((Functor.const Cᵒᵖ).obj M ⟶ productPresheaf F P) ≃ (M ⟶ P.obj (op F)) where
  toFun := toFrame F P M
  invFun := fromFrame F P M
  left_inv := fromFrame_toFrame F P M
  right_inv := toFrame_fromFrame F P M

variable (R : Type t) [CommRing R] [Preadditive D] [Linear R D]

def homLinearEquiv : ((Functor.const Cᵒᵖ).obj M ⟶ productPresheaf F P) ≃ₗ[R] (M ⟶ P.obj (op F)) :=
  { homEquiv F P M with
    map_add' := by
      intro a b
      change (a.app (op F) + b.app (op F)) ≫ P.map (prod.lift (𝟙 F) (𝟙 F)).op = _
      rw [Preadditive.add_comp]
      rfl
    map_smul' := by
      intro r a
      exact Linear.smul_comp _ _ _ r (a.app (op F)) (P.map (prod.lift (𝟙 F) (𝟙 F)).op) }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProductPresheafSections
