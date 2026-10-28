import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Descent Square Isomorphisms -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareIsomorphisms

noncomputable section

/-!
# Canonical isomorphisms for a square of ordinary descent covers
-/

open _root_.CategoryTheory Opposite

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iX : X' ⟶ X) (iY : Y' ⟶ Y) (hf : iX ≫ f = f' ≫ iY)

/-- Native pullback of ordinary descent data on a single cover. -/
def squareFunctor : F.DescentData (fun (_ : PUnit.{1}) => f) ⥤
    F.DescentData (fun (_ : PUnit.{1}) => f') :=
  Pseudofunctor.DescentData.pullFunctor F
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := iY)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => iX) (fun _ => hf)

/-- The canonical descent of a pulled object is canonically the pullback of its descent datum. -/
def canonicalIso (P : F.obj (.mk (op Y))) :
    (squareFunctor F f f' iX iY hf).obj
      (Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f) P) ≅
    Pseudofunctor.DescentData.ofObj (F := F) (f := fun (_ : PUnit.{1}) => f')
      ((F.map iY.op.toLoc).toFunctor.obj P) :=
  (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
    (f := fun (_ : PUnit.{1}) => f) (f' := fun (_ : PUnit.{1}) => f') (p := iY)
    (α := fun (_ : PUnit.{1}) => PUnit.unit) (p' := fun (_ : PUnit.{1}) => iX) (fun _ => hf)).app P

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareIsomorphisms
