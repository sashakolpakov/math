import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocycleLinearizationSelf

/-! # Cocycle Point Transport -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A relation linearization transports along arbitrary actual relation
points, before a quotient exists. This is the form preserved by scalar
change of the quotient presentation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {B T X : C} (u : T ⟶ B) (a : X ⟶ T)
    (t : DescentCocycleChange.DescentCocycle.overlap u a ⟶ X) (ht : t ≫ a = DescentCocycleChange.DescentCocycle.base u a)
    (hn : DescentCocycleChange.DescentCocycle.diagonal u a ≫ t = 𝟙 X)
    (hc : DescentCocycleChange.DescentCocycle.composition u a t ht ≫ t = pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ t)
    (L : F.obj (.mk (op X))) (D : CocycleLinearizationSelf.CocycleLinearization F u a t ht hn hc L)

include ht in
theorem CocycleLinearizationSelf.CocycleLinearization.relation_ext {Z : C} (r r' : Z ⟶ DescentCocycleChange.DescentCocycle.overlap u a)
    (hs : r ≫ DescentCocycleChange.DescentCocycle.source u a = r' ≫ DescentCocycleChange.DescentCocycle.source u a)
    (he : r ≫ t = r' ≫ t) : r = r' := by
  apply pullback.hom_ext hs
  change r ≫ DescentCocycleChange.DescentCocycle.base u a = r' ≫ DescentCocycleChange.DescentCocycle.base u a
  rw [← ht, ← Category.assoc, ← Category.assoc, he]

def CocycleLinearizationSelf.CocycleLinearization.pointHom {Z : C} (r : Z ⟶ DescentCocycleChange.DescentCocycle.overlap u a) (x y : Z ⟶ X)
    (hs : r ≫ DescentCocycleChange.DescentCocycle.source u a = x) (he : r ≫ t = y) :
    (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj L :=
  pullHom D.iso.hom r x y hs he

theorem CocycleLinearizationSelf.CocycleLinearization.pointHom_self {Z : C} (r : Z ⟶ DescentCocycleChange.DescentCocycle.overlap u a) (x : Z ⟶ X)
    (hs : r ≫ DescentCocycleChange.DescentCocycle.source u a = x) (he : r ≫ t = x) :
    D.pointHom F u a t ht hn hc L r x x hs he = 𝟙 _ := by
  have hr : r = x ≫ DescentCocycleChange.DescentCocycle.diagonal u a := by
    apply CocycleLinearizationSelf.CocycleLinearization.relation_ext u a t ht
    · simpa only [Category.assoc, DescentCocycleChange.DescentCocycle.diagonal_source, Category.comp_id] using hs
    · simpa only [Category.assoc, hn, Category.comp_id] using he
  have hi := congrArg (fun φ => pullHom φ x x x (Category.comp_id x) (Category.comp_id x)) D.identity
  rw [Picard.PoincareBundle.PullHom.pullHom_identity] at hi
  exact (Picard.PoincareBundle.PullHom.pullHom_congr D.iso.hom _ _ hr x x _ _ _ _).trans
    ((pullHom_pullHom D.iso.hom (DescentCocycleChange.DescentCocycle.diagonal u a) (𝟙 X) (𝟙 X) x x x
      (DescentCocycleChange.DescentCocycle.diagonal_source u a) hn (Category.comp_id x) (Category.comp_id x)).symm.trans hi)

theorem CocycleLinearizationSelf.CocycleLinearization.pointHom_restrict {Z Z' : C} (r : Z ⟶ DescentCocycleChange.DescentCocycle.overlap u a) (x y : Z ⟶ X)
    (hs : r ≫ DescentCocycleChange.DescentCocycle.source u a = x) (he : r ≫ t = y)
    (g : Z' ⟶ Z) (r' : Z' ⟶ DescentCocycleChange.DescentCocycle.overlap u a) (x' y' : Z' ⟶ X)
    (hr : g ≫ r = r') (hx : g ≫ x = x') (hy : g ≫ y = y')
    (hs' : r' ≫ DescentCocycleChange.DescentCocycle.source u a = x') (he' : r' ≫ t = y') :
    pullHom (D.pointHom F u a t ht hn hc L r x y hs he) g x' y' hx hy =
      D.pointHom F u a t ht hn hc L r' x' y' hs' he' :=
  (pullHom_pullHom D.iso.hom r x y g x' y' hs he hx hy).trans
    (Picard.PoincareBundle.PullHom.pullHom_congr D.iso.hom _ _ hr x' y' _ _ hs' he')

theorem CocycleLinearizationSelf.CocycleLinearization.pointHom_trans {Z : C} (r₁ r₂ r₃ : Z ⟶ DescentCocycleChange.DescentCocycle.overlap u a) (x y z : Z ⟶ X)
    (hs₁ : r₁ ≫ DescentCocycleChange.DescentCocycle.source u a = x) (ht₁ : r₁ ≫ t = y)
    (hs₂ : r₂ ≫ DescentCocycleChange.DescentCocycle.source u a = y) (ht₂ : r₂ ≫ t = z)
    (hs₃ : r₃ ≫ DescentCocycleChange.DescentCocycle.source u a = x) (ht₃ : r₃ ≫ t = z) :
    D.pointHom F u a t ht hn hc L r₁ x y hs₁ ht₁ ≫
      D.pointHom F u a t ht hn hc L r₂ y z hs₂ ht₂ =
      D.pointHom F u a t ht hn hc L r₃ x z hs₃ ht₃ := by
  let src := DescentCocycleChange.DescentCocycle.source u a
  let k := pullback.lift r₁ r₂ (ht₁.trans hs₂.symm)
  have hk₁ : k ≫ pullback.fst t src = r₁ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd t src = r₂ := pullback.lift_snd _ _ _
  let c := DescentCocycleChange.DescentCocycle.composition u a t ht
  have hk₃ : k ≫ c = r₃ := by
    apply CocycleLinearizationSelf.CocycleLinearization.relation_ext u a t ht
    · rw [Category.assoc, DescentCocycleChange.DescentCocycle.composition_source, ← Category.assoc, hk₁]
      exact hs₁.trans hs₃.symm
    · rw [Category.assoc, hc, ← Category.assoc, hk₂]
      exact ht₂.trans ht₃.symm
  have hs : k ≫ (pullback.fst t src ≫ src) = x := by rw [← Category.assoc, hk₁]; exact hs₁
  have hm : k ≫ (pullback.snd t src ≫ src) = y := by rw [← Category.assoc, hk₂]; exact hs₂
  have he : k ≫ (pullback.snd t src ≫ t) = z := by rw [← Category.assoc, hk₂]; exact ht₂
  have H := congrArg (fun φ => pullHom φ k x z hs he) D.cocycle
  rw [Picard.PoincareBundle.PullHom.pullHom_comp _ _ k x y z hs hm he] at H
  have H₁ := pullHom_pullHom D.iso.hom (pullback.fst t src)
    (pullback.fst t src ≫ src) (pullback.snd t src ≫ src) k x y rfl pullback.condition hs hm
  have H₂ := pullHom_pullHom D.iso.hom (pullback.snd t src)
    (pullback.snd t src ≫ src) (pullback.snd t src ≫ t) k y z rfl rfl hm he
  have H₃ := pullHom_pullHom D.iso.hom c
    (pullback.fst t src ≫ src) (pullback.snd t src ≫ t) k x z
    (DescentCocycleChange.DescentCocycle.composition_source u a t ht) hc hs he
  rw [H₁, H₂, H₃] at H
  simpa only [CocycleLinearizationSelf.CocycleLinearization.pointHom, hk₁, hk₂, hk₃] using H

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
