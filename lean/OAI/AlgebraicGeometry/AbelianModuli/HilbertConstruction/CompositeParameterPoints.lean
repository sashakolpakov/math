import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Logic.Equiv.Sum

/-! # Composite Parameter Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompositeParameterPoints

noncomputable section

/-! Points of a relative parameter viewed over the original base are exactly a base parameter point together with a relative parameter point over it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (M : Over S) (R : Over M.left)

def compositeParameterProjection : (Over.map M.hom).obj R ⟶ M :=
  Over.homMk R.hom rfl

def compositeParameterFiberEquiv (T : Over S) (c : T ⟶ M) :
    {y : T ⟶ (Over.map M.hom).obj R // y ≫ compositeParameterProjection M R = c} ≃
      (Over.mk c.left ⟶ R) where
  toFun y := Over.homMk y.val.left (congrArg Over.Hom.left y.property)
  invFun z :=
    ⟨Over.homMk z.left ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ M.hom) z.w).trans c.w)), Over.OverMorphism.ext z.w⟩
  left_inv _ := Subtype.ext (Over.OverMorphism.ext rfl)
  right_inv _ := Over.OverMorphism.ext rfl

def compositeParameterPointEquiv (T : Over S) :
    (T ⟶ (Over.map M.hom).obj R) ≃ Σ c : T ⟶ M, (Over.mk c.left ⟶ R) :=
  (Equiv.sigmaFiberEquiv (fun y : T ⟶ (Over.map M.hom).obj R =>
    y ≫ compositeParameterProjection M R)).symm.trans
      (Equiv.sigmaCongrRight (compositeParameterFiberEquiv M R T))

theorem compositeParameterPointEquiv_base (T : Over S) (y : T ⟶ (Over.map M.hom).obj R) :
    (compositeParameterPointEquiv M R T y).1 = y ≫ compositeParameterProjection M R := rfl

theorem compositeParameterPointEquiv_relative_left (T : Over S) (y : T ⟶ (Over.map M.hom).obj R) :
    (compositeParameterPointEquiv M R T y).2.left = y.left := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CompositeParameterPoints
