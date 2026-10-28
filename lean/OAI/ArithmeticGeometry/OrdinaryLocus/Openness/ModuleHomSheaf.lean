import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleDescent
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Module Hom Sheaf -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction

noncomputable section

/-! The sheaf of local linear morphisms between two module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem linearity_after_restriction
    {C : Type v} [Category.{u} C] {A B A' B' : C}
    (a : A ⟶ A) (b : B ⟶ B) (a' : A' ⟶ A') (b' : B' ⟶ B')
    (q : A ⟶ B) (q' : A' ⟶ B') (i : A ⟶ A') (j : B ⟶ B')
    (hi : a ≫ i = i ≫ a') (hj : b ≫ j = j ≫ b')
    (hq : i ≫ q' = q ≫ j) (h : a' ≫ q' = q' ≫ b') :
    (a ≫ q) ≫ j = (q ≫ b) ≫ j := by
  rw [Category.assoc, ← hq, ← Category.assoc, hi, Category.assoc, h,
    ← Category.assoc, hq, Category.assoc, ← hj, ← Category.assoc]

def moduleHomSubfunctor {X : Scheme.{u}} (M N : X.Modules) :
    Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := {q | ∀ V : Over U.unop, ∀ r : Γ(X, V.left),
    M.smul r ≫ q.app (.op V) = q.app (.op V) ≫ N.smul r}
  map := by
    intro U V f q hq W r
    exact hq ((Over.map f.unop).obj W) r

theorem isSheaf_moduleHomSubfunctor {X : Scheme.{u}} (M N : X.Modules) :
    Presheaf.IsSheaf (_root_.Opens.grothendieckTopology X)
      (moduleHomSubfunctor M N).toFunctor := by
  let J := _root_.Opens.grothendieckTopology X
  have hN : Presheaf.IsSheaf J N.presheaf := SheafOfModules.isSheaf N
  have hHom := (isSheaf_iff_isSheaf_of_type J _).mp (hN.hom M.presheaf)
  rw [isSheaf_iff_isSheaf_of_type,
    (moduleHomSubfunctor M N).isSheaf_iff hHom]
  intro U q hq V r
  change (Over.forget U.unop).op ⋙ M.presheaf ⟶
    (Over.forget U.unop).op ⋙ N.presheaf at q
  let S := (moduleHomSubfunctor M N).sieveOfSection q
  let T : J.Cover V.left := ⟨S.pullback V.hom, J.pullback_stable V.hom hq⟩
  apply hN.hom_ext T
  intro I
  let W : Over U.unop := Over.mk (I.f ≫ V.hom)
  let j : W ⟶ V := Over.homMk I.f
  have hn : M.presheaf.map I.f.op ≫ q.app (.op W) =
      q.app (.op V) ≫ N.presheaf.map I.f.op := q.naturality j.op
  have hlin : M.smul (X.presheaf.map I.f.op r) ≫ q.app (.op W) =
      q.app (.op W) ≫ N.smul (X.presheaf.map I.f.op r) := by
    have hi := I.hf
    change ∀ Z : Over I.Y, ∀ a : Γ(X, Z.left),
      M.smul a ≫ ((presheafHom M.presheaf N.presheaf).map (I.f ≫ V.hom).op q).app (.op Z) =
        ((presheafHom M.presheaf N.presheaf).map (I.f ≫ V.hom).op q).app (.op Z) ≫ N.smul a at hi
    have h := hi (Over.mk (𝟙 I.Y)) (X.presheaf.map I.f.op r)
    have he : ((presheafHom M.presheaf N.presheaf).map (I.f ≫ V.hom).op q).app
        (.op (Over.mk (𝟙 I.Y))) = q.app (.op W) :=
      presheafHom_map_app_op_mk_id (I.f ≫ V.hom) q
    exact (congrArg (fun t ↦ M.smul (X.presheaf.map I.f.op r) ≫ t) he).symm.trans
      (h.trans (congrArg (fun t ↦ t ≫ N.smul (X.presheaf.map I.f.op r)) he))
  exact linearity_after_restriction _ _ _ _ _ _ _ _
    (Scheme.Modules.map_comp_smul (M := M) I.f r)
    (Scheme.Modules.map_comp_smul (M := N) I.f r) hn hlin

def moduleHomTypeSheaf {X : Scheme.{u}} (M N : X.Modules) :
    Sheaf (_root_.Opens.grothendieckTopology X) (Type u) :=
  ⟨(moduleHomSubfunctor M N).toFunctor, isSheaf_moduleHomSubfunctor M N⟩

def moduleHomToOver {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (q : (moduleHomSubfunctor M N).toFunctor.obj (.op U)) : M.over U ⟶ N.over U where
  val :=
    { app V := ModuleCat.ofHom (R := X.ringCatSheaf.obj.obj (.op V.unop.left))
        (X := M.val.obj (.op V.unop.left)) (Y := N.val.obj (.op V.unop.left))
        { toFun := q.1.app V
          map_add' := (q.1.app V).hom.map_add
          map_smul' r m := congrArg (fun a ↦ a m) (q.2 V.unop r) }
      naturality {V W} h := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact congrArg (fun a ↦ a m) (q.1.naturality h) }

def moduleHomFromOver {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (q : M.over U ⟶ N.over U) : (moduleHomSubfunctor M N).toFunctor.obj (.op U) := by
  refine ⟨{ app := fun V ↦ (forget₂ _ AddCommGrpCat).map (q.val.app V)
            naturality := ?_ }, ?_⟩
  · intro V W h
    ext m
    exact PresheafOfModules.naturality_apply q.val h m
  · intro V r
    ext m
    exact (q.val.app (.op V)).hom.map_smul r m

def moduleHomOverEquiv {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens) :
    (moduleHomSubfunctor M N).toFunctor.obj (.op U) ≃ (M.over U ⟶ N.over U) where
  toFun := moduleHomToOver M N U
  invFun := moduleHomFromOver M N U
  left_inv q := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext m
    rfl
  right_inv q := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleHomSheaf.Construction
