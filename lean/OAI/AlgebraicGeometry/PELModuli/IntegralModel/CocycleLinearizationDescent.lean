import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocycleLinearizationSelf

/-! # Cocycle Linearization Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A proved relation cocycle gives compatible transport on all test
objects, hence ordinary module descent data for the actual quotient. -/

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
    {Y : C} (q : X ⟶ Y) (hk : IsKernelPair q (DescentCocycleChange.DescentCocycle.source u a) t)

theorem CocycleLinearizationSelf.CocycleLinearization.transport_trans {Z : C} (x y z : Z ⟶ X)
    (hxy : x ≫ q = y ≫ q) (hyz : y ≫ q = z ≫ q) :
    D.transport F u a t ht hn hc L q hk x y hxy ≫
      D.transport F u a t ht hn hc L q hk y z hyz =
      D.transport F u a t ht hn hc L q hk x z (hxy.trans hyz) := by
  let src := DescentCocycleChange.DescentCocycle.source u a
  let r₁ := hk.lift x y hxy
  let r₂ := hk.lift y z hyz
  let r₃ := hk.lift x z (hxy.trans hyz)
  let k := pullback.lift r₁ r₂ ((hk.lift_snd x y hxy).trans (hk.lift_fst y z hyz).symm)
  have hk₁ : k ≫ pullback.fst t src = r₁ := pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd t src = r₂ := pullback.lift_snd _ _ _
  let c := DescentCocycleChange.DescentCocycle.composition u a t ht
  have hk₃ : k ≫ c = r₃ := by
    apply hk.hom_ext
    · change (k ≫ c) ≫ src = r₃ ≫ src
      rw [Category.assoc, DescentCocycleChange.DescentCocycle.composition_source, ← Category.assoc, hk₁]
      exact (hk.lift_fst _ _ _).trans (hk.lift_fst _ _ _).symm
    · rw [Category.assoc, hc, ← Category.assoc, hk₂]
      exact (hk.lift_snd _ _ _).trans (hk.lift_snd _ _ _).symm
  have hs : k ≫ (pullback.fst t src ≫ src) = x := by
    rw [← Category.assoc, hk₁]
    exact hk.lift_fst _ _ _
  have hm : k ≫ (pullback.snd t src ≫ src) = y := by
    rw [← Category.assoc, hk₂]
    exact hk.lift_fst _ _ _
  have he : k ≫ (pullback.snd t src ≫ t) = z := by
    rw [← Category.assoc, hk₂]
    exact hk.lift_snd _ _ _
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
  simpa only [CocycleLinearizationSelf.CocycleLinearization.transport, hk₁, hk₂, hk₃] using H

def CocycleLinearizationSelf.CocycleLinearization.descentData : F.DescentData (fun (_ : PUnit.{1}) => q) where
  obj _ := L
  hom := fun {_Z} _ {_i _j} x y hx hy => D.transport F u a t ht hn hc L q hk x y (hx.trans hy.symm)
  pullHom_hom := fun {_Z' _Z} g _ _ _ {_i _j} x y hx hy x' y' hx' hy' =>
    D.transport_restrict F u a t ht hn hc L q hk x y (hx.trans hy.symm) g x' y' hx' hy' _
  hom_self := fun {_Z} _ {_i} x _ => D.transport_self F u a t ht hn hc L q hk x
  hom_comp := fun {_Z} _ {_i _j _k} x y z hx hy hz => D.transport_trans F u a t ht hn hc L q hk x y z
    (hx.trans hy.symm) (hy.trans hz.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
