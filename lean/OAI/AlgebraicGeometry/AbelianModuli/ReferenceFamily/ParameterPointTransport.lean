import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison

/-! # Parameter Point Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterPointTransport

noncomputable section

/-! A test scheme mapping to a parameter scheme has its literal
structure over that parameter. The pullback point equivalence keeps
the original group-valued point and is natural in the test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) (P : Over S)

def parameterTestIso (X : Over S) (t : X ⟶ P) :
    (Over.map P.hom).obj (Over.mk t.left) ≅ X :=
  AbelianScheme.IsogenyQuotient.Parameter.TestComparison.Construction.parameterTestIso t

def parameterOriginalPointEquiv (X : Over S) (t : X ⟶ P) :
    (X ⟶ G.X) ≃* ((Over.map P.hom).obj (Over.mk t.left) ⟶ G.X) where
  toFun a := (parameterTestIso P X t).hom ≫ a
  invFun a := (parameterTestIso P X t).inv ≫ a
  left_inv a := by
    change (parameterTestIso P X t).inv ≫ ((parameterTestIso P X t).hom ≫ a) = a
    rw [← Category.assoc, (parameterTestIso P X t).inv_hom_id, Category.id_comp]
  right_inv a := by
    change (parameterTestIso P X t).hom ≫ ((parameterTestIso P X t).inv ≫ a) = a
    rw [← Category.assoc, (parameterTestIso P X t).hom_inv_id, Category.id_comp]
  map_mul' a b := MonObj.comp_mul _ a b

def parameterPointMulEquiv (X : Over S) (t : X ⟶ P) :
    (X ⟶ G.X) ≃* (Over.mk t.left ⟶ (Over.pullback P.hom).obj G.X) :=
  (parameterOriginalPointEquiv G P X t).trans (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left))

theorem parameterPointMulEquiv_fst (X : Over S) (t : X ⟶ P) (a : X ⟶ G.X) :
    (parameterPointMulEquiv G P X t a).left ≫ pullback.fst G.X.hom P.hom = a.left := by
  have h := congrArg Over.Hom.left
    ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm_apply_apply
      ((parameterTestIso P X t).hom ≫ a))
  change (parameterPointMulEquiv G P X t a).left ≫ pullback.fst G.X.hom P.hom =
    (𝟙 X.left) ≫ a.left at h
  exact h.trans (Category.id_comp _)

theorem parameterPointMulEquiv_symm_left (X : Over S) (t : X ⟶ P)
    (a : Over.mk t.left ⟶ (Over.pullback P.hom).obj G.X) :
    ((parameterPointMulEquiv G P X t).symm a).left =
      a.left ≫ pullback.fst G.X.hom P.hom := by
  have h := parameterPointMulEquiv_fst G P X t ((parameterPointMulEquiv G P X t).symm a)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

def parameterTestMap {X Y : Over S} (a : X ⟶ Y) (t : Y ⟶ P) :
    Over.mk (a ≫ t).left ⟶ Over.mk t.left := Over.homMk a.left rfl

theorem parameterPointMulEquiv_natural {X Y : Over S}
    (a : X ⟶ Y) (t : Y ⟶ P) (x : Y ⟶ G.X) :
    parameterPointMulEquiv G P X (a ≫ t) (a ≫ x) =
      parameterTestMap P a t ≫ parameterPointMulEquiv G P Y t x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (parameterPointMulEquiv G P X (a ≫ t) (a ≫ x)).left ≫
        pullback.fst G.X.hom P.hom =
      (a.left ≫ (parameterPointMulEquiv G P Y t x).left) ≫ pullback.fst G.X.hom P.hom
    rw [parameterPointMulEquiv_fst, Category.assoc, parameterPointMulEquiv_fst]
    rfl
  · exact (parameterPointMulEquiv G P X (a ≫ t) (a ≫ x)).w.trans
      (parameterTestMap P a t ≫ parameterPointMulEquiv G P Y t x).w.symm

theorem parameterPointMulEquiv_canonical (X : Over P.left)
    (x : (Over.map P.hom).obj X ⟶ G.X) :
    parameterPointMulEquiv G P ((Over.map P.hom).obj X) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P X) x =
      AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G X x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hx := congrArg Over.Hom.left ((AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G X).symm_apply_apply x)
    exact (parameterPointMulEquiv_fst G P _ _ x).trans hx.symm
  · exact (parameterPointMulEquiv G P _ _ x).w.trans (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G X x).w.symm

theorem parameterPointMulEquiv_comp (c : G ⟶ G) (X : Over S)
    (t : X ⟶ P) (x : X ⟶ G.X) :
    parameterPointMulEquiv G P X t (x ≫ c.hom.hom) =
      parameterPointMulEquiv G P X t x ≫ (Over.pullback P.hom).map c.hom.hom := by
  apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm.injective
  have hr := AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom c (Over.mk t.left)
    (parameterPointMulEquiv G P X t x)
  have hx : (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm
      (parameterPointMulEquiv G P X t x) = (parameterTestIso P X t).hom ≫ x :=
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm_apply_apply _
  have hxc : (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm
      (parameterPointMulEquiv G P X t (x ≫ c.hom.hom)) =
        (parameterTestIso P X t).hom ≫ (x ≫ c.hom.hom) :=
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G (Over.mk t.left)).symm_apply_apply _
  exact hxc.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ c.hom.hom) hx).symm.trans hr.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ParameterPointTransport
