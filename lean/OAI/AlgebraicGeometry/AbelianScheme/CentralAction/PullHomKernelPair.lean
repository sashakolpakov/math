import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Pull Hom Kernel Pair -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomKernelPair.Construction

noncomputable section

/-! Compatibility on the actual kernel pair implies compatibility on
all test objects, with pullback associativity retained. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

theorem pullHom_compatible_of_kernel_pair
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {X Y : C} (f : X ⟶ Y) {L M : F.obj (.mk (.op Y))}
    (a : (F.map f.op.toLoc).toFunctor.obj L ⟶ (F.map f.op.toLoc).toFunctor.obj M)
    (ha : pullHom a (pullback.fst f f) (pullback.fst f f ≫ f)
        (pullback.fst f f ≫ f) rfl rfl =
      pullHom a (pullback.snd f f) (pullback.fst f f ≫ f)
        (pullback.fst f f ≫ f) pullback.condition.symm pullback.condition.symm)
    {T : C} (p q : T ⟶ X) (hpq : p ≫ f = q ≫ f) :
    pullHom a p (p ≫ f) (p ≫ f) rfl rfl =
      pullHom a q (p ≫ f) (p ≫ f) hpq.symm hpq.symm := by
  let t := pullback.lift p q hpq
  have ht : t ≫ (pullback.fst f f ≫ f) = p ≫ f := by
    rw [← Category.assoc, pullback.lift_fst]
  have H := congrArg (fun b => pullHom b t (p ≫ f) (p ≫ f) ht ht) ha
  rw [pullHom_pullHom, pullHom_pullHom] at H
  have ht₁ : t ≫ pullback.fst f f = p := pullback.lift_fst p q hpq
  have ht₂ : t ≫ pullback.snd f f = q := pullback.lift_snd p q hpq
  simpa only [ht₁, ht₂] using H

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomKernelPair.Construction
