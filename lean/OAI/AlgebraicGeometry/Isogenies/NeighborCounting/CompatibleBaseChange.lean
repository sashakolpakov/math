import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Compatible Base Change -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompatibleBaseChange

noncomputable section

/-! Compatibility of a pullback morphism is preserved by changing the
base, with the pseudofunctor composition comparisons retained. -/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {X Y X' Y' : C} {M N : F.obj (.mk (op Y))}

def Compatible (f : X ⟶ Y)
    (q : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N) : Prop :=
  ∀ {T : C} (x y : T ⟶ X) (p : T ⟶ Y) (hx : x ≫ f = p) (hy : y ≫ f = p),
    pullHom q x p p hx hx = pullHom q y p p hy hy

def baseHom (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    (h : i ≫ f = g ≫ j)
    (q : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N) :
    (F.map g.op.toLoc).toFunctor.obj ((F.map j.op.toLoc).toFunctor.obj M) ⟶
      (F.map g.op.toLoc).toFunctor.obj ((F.map j.op.toLoc).toFunctor.obj N) :=
  (F.overMapCompPresheafHomIso M N j).hom.app (op (Over.mk g))
    (pullHom q i (g ≫ j) (g ≫ j) h h)

theorem baseHom_compatible (f : X ⟶ Y) (g : X' ⟶ Y') (i : X' ⟶ X) (j : Y' ⟶ Y)
    (h : i ≫ f = g ≫ j)
    (q : (F.map f.op.toLoc).toFunctor.obj M ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (hq : Compatible f q) : Compatible g (baseHom f g i j h q) := by
  intro T x y p hx hy
  let φ := F.overMapCompPresheafHomIso M N j
  let qr := pullHom q i (g ≫ j) (g ≫ j) h h
  have hx' : x ≫ (g ≫ j) = p ≫ j := by rw [← Category.assoc, hx]
  have hy' : y ≫ (g ≫ j) = p ≫ j := by rw [← Category.assoc, hy]
  have hxi : (x ≫ i) ≫ f = p ≫ j := by rw [Category.assoc, h, hx']
  have hyi : (y ≫ i) ≫ f = p ≫ j := by rw [Category.assoc, h, hy']
  have hqr : pullHom qr x (p ≫ j) (p ≫ j) hx' hx' =
      pullHom qr y (p ≫ j) (p ≫ j) hy' hy' :=
    (pullHom_pullHom q i (g ≫ j) (g ≫ j) x (p ≫ j) (p ≫ j) h h hx' hx').trans
      ((hq (x ≫ i) (y ≫ i) (p ≫ j) hxi hyi).trans
        (pullHom_pullHom q i (g ≫ j) (g ≫ j) y (p ≫ j) (p ≫ j) h h hy' hy').symm)
  let ax : Over.mk p ⟶ Over.mk g := Over.homMk x hx
  let ay : Over.mk p ⟶ Over.mk g := Over.homMk y hy
  have hnx := φ.hom.naturality_apply ax.op qr
  have hny := φ.hom.naturality_apply ay.op qr
  exact hnx.symm.trans ((congrArg (fun r ↦ φ.hom.app (op (Over.mk p)) r) hqr).trans hny)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompatibleBaseChange
