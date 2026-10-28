import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DescentCocycleChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Cocycle Linearization Self -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocycleLinearizationSelf

noncomputable section

/-! Ordinary descent data constructed from a genuine isomorphism on
the prescribed relation and its proved diagonal and triple equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {B T X : C} (u : T ⟶ B) (a : X ⟶ T)
    (t : DescentCocycleChange.DescentCocycle.overlap u a ⟶ X) (ht : t ≫ a = DescentCocycleChange.DescentCocycle.base u a)
    (hn : DescentCocycleChange.DescentCocycle.diagonal u a ≫ t = 𝟙 X)
    (hc : DescentCocycleChange.DescentCocycle.composition u a t ht ≫ t = pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ t)
    (L : F.obj (.mk (op X)))

structure CocycleLinearization where
  iso : (F.map (DescentCocycleChange.DescentCocycle.source u a).op.toLoc).toFunctor.obj L ≅
    (F.map t.op.toLoc).toFunctor.obj L
  identity : pullHom iso.hom (DescentCocycleChange.DescentCocycle.diagonal u a) (𝟙 X) (𝟙 X)
    (DescentCocycleChange.DescentCocycle.diagonal_source u a) hn = 𝟙 _
  cocycle :
    pullHom iso.hom (pullback.fst t (DescentCocycleChange.DescentCocycle.source u a))
        (pullback.fst t (DescentCocycleChange.DescentCocycle.source u a) ≫ DescentCocycleChange.DescentCocycle.source u a)
        (pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ DescentCocycleChange.DescentCocycle.source u a) rfl pullback.condition ≫
      pullHom iso.hom (pullback.snd t (DescentCocycleChange.DescentCocycle.source u a))
        (pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ DescentCocycleChange.DescentCocycle.source u a)
        (pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ t) rfl rfl =
      pullHom iso.hom (DescentCocycleChange.DescentCocycle.composition u a t ht)
        (pullback.fst t (DescentCocycleChange.DescentCocycle.source u a) ≫ DescentCocycleChange.DescentCocycle.source u a)
        (pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ t)
        (DescentCocycleChange.DescentCocycle.composition_source u a t ht) hc

namespace CocycleLinearization
variable (D : CocycleLinearization F u a t ht hn hc L)
    {Y : C} (q : X ⟶ Y) (hk : IsKernelPair q (DescentCocycleChange.DescentCocycle.source u a) t)

def transport {Z : C} (x y : Z ⟶ X) (h : x ≫ q = y ≫ q) :
    (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj L :=
  pullHom D.iso.hom (hk.lift x y h) x y (hk.lift_fst _ _ _) (hk.lift_snd _ _ _)

theorem transport_restrict {Z Z' : C} (x y : Z ⟶ X) (h : x ≫ q = y ≫ q)
    (g : Z' ⟶ Z) (x' y' : Z' ⟶ X) (hx : g ≫ x = x') (hy : g ≫ y = y')
    (h' : x' ≫ q = y' ≫ q) :
    pullHom (D.transport F u a t ht hn hc L q hk x y h) g x' y' hx hy =
      D.transport F u a t ht hn hc L q hk x' y' h' := by
  have hp : g ≫ hk.lift x y h = hk.lift x' y' h' := by
    apply hk.hom_ext <;> simp only [Category.assoc, hk.lift_fst, hk.lift_snd, hx, hy]
  exact (pullHom_pullHom D.iso.hom (hk.lift x y h) x y g x' y'
    (hk.lift_fst _ _ _) (hk.lift_snd _ _ _) hx hy).trans
      (Picard.PoincareBundle.PullHom.pullHom_congr D.iso.hom _ _ hp x' y' _ _ _ _)

theorem transport_self {Z : C} (x : Z ⟶ X) :
    D.transport F u a t ht hn hc L q hk x x rfl = 𝟙 _ := by
  have hp : hk.lift x x rfl = x ≫ DescentCocycleChange.DescentCocycle.diagonal u a := by
    apply hk.hom_ext <;> simp only [Category.assoc, hk.lift_fst, hk.lift_snd,
      DescentCocycleChange.DescentCocycle.diagonal_source, hn, Category.comp_id]
  have hi := congrArg (fun φ => pullHom φ x x x (Category.comp_id x) (Category.comp_id x)) D.identity
  rw [Picard.PoincareBundle.PullHom.pullHom_identity] at hi
  exact (Picard.PoincareBundle.PullHom.pullHom_congr D.iso.hom _ _ hp x x _ _ _ _).trans
    ((pullHom_pullHom D.iso.hom (DescentCocycleChange.DescentCocycle.diagonal u a) (𝟙 X) (𝟙 X) x x x
      (DescentCocycleChange.DescentCocycle.diagonal_source u a) hn (Category.comp_id x) (Category.comp_id x)).symm.trans hi)

end CocycleLinearization

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocycleLinearizationSelf
