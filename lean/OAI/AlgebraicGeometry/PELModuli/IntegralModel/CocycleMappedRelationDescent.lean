import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocyclePointTransport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackPointMorphism

/-! # Cocycle Mapped Relation Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! A quotient whose relation maps to a proved linearized relation
inherits ordinary descent data on the pulled-back object. This permits
scalar change without constructing a quotient before scalar change. -/

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
    {X' R' Y : C} (v : X' ⟶ X) (s' t' : R' ⟶ X') (ρ : R' ⟶ DescentCocycleChange.DescentCocycle.overlap u a)
    (hρs : ρ ≫ DescentCocycleChange.DescentCocycle.source u a = s' ≫ v) (hρt : ρ ≫ t = t' ≫ v)
    (q : X' ⟶ Y) (hk : IsKernelPair q s' t')

include hρs in
theorem CocycleLinearizationSelf.CocycleLinearization.mappedRelation_source {Z : C} (x y : Z ⟶ X') (h : x ≫ q = y ≫ q) :
    (hk.lift x y h ≫ ρ) ≫ DescentCocycleChange.DescentCocycle.source u a = x ≫ v := by
  rw [Category.assoc, hρs, ← Category.assoc, hk.lift_fst]

include hρt in
theorem CocycleLinearizationSelf.CocycleLinearization.mappedRelation_target {Z : C} (x y : Z ⟶ X') (h : x ≫ q = y ≫ q) :
    (hk.lift x y h ≫ ρ) ≫ t = y ≫ v := by
  rw [Category.assoc, hρt, ← Category.assoc, hk.lift_snd]

def CocycleLinearizationSelf.CocycleLinearization.mappedTransport {Z : C} (x y : Z ⟶ X') (h : x ≫ q = y ≫ q) :
    (F.map x.op.toLoc).toFunctor.obj ((F.map v.op.toLoc).toFunctor.obj L) ⟶
      (F.map y.op.toLoc).toFunctor.obj ((F.map v.op.toLoc).toFunctor.obj L) :=
  PullbackPointMorphism.pullbackPointMorphism F v L x y
    (D.pointHom F u a t ht hn hc L (hk.lift x y h ≫ ρ) (x ≫ v) (y ≫ v)
      (CocycleLinearizationSelf.CocycleLinearization.mappedRelation_source u a v s' t' ρ hρs q hk x y h)
      (CocycleLinearizationSelf.CocycleLinearization.mappedRelation_target u a t v s' t' ρ hρt q hk x y h))

theorem CocycleLinearizationSelf.CocycleLinearization.mappedTransport_self {Z : C} (x : Z ⟶ X') :
    D.mappedTransport F u a t ht hn hc L v s' t' ρ hρs hρt q hk x x rfl = 𝟙 _ := by
  unfold CocycleLinearizationSelf.CocycleLinearization.mappedTransport
  rw [D.pointHom_self F u a t ht hn hc L, PullbackPointMorphism.pullbackPointMorphism_identity]

theorem CocycleLinearizationSelf.CocycleLinearization.mappedTransport_trans {Z : C} (x y z : Z ⟶ X')
    (hxy : x ≫ q = y ≫ q) (hyz : y ≫ q = z ≫ q) :
    D.mappedTransport F u a t ht hn hc L v s' t' ρ hρs hρt q hk x y hxy ≫
      D.mappedTransport F u a t ht hn hc L v s' t' ρ hρs hρt q hk y z hyz =
      D.mappedTransport F u a t ht hn hc L v s' t' ρ hρs hρt q hk x z (hxy.trans hyz) := by
  unfold CocycleLinearizationSelf.CocycleLinearization.mappedTransport
  rw [PullbackPointMorphism.pullbackPointMorphism_comp]
  exact congrArg (PullbackPointMorphism.pullbackPointMorphism F v L x z)
    (D.pointHom_trans F u a t ht hn hc L _ _ _ (x ≫ v) (y ≫ v) (z ≫ v) _ _ _ _ _ _)

theorem CocycleLinearizationSelf.CocycleLinearization.mappedTransport_restrict {Z Z' : C} (x y : Z ⟶ X') (h : x ≫ q = y ≫ q)
    (g : Z' ⟶ Z) (x' y' : Z' ⟶ X') (hx : g ≫ x = x') (hy : g ≫ y = y')
    (h' : x' ≫ q = y' ≫ q) :
    pullHom (D.mappedTransport F u a t ht hn hc L v s' t' ρ hρs hρt q hk x y h) g x' y' hx hy =
      D.mappedTransport F u a t ht hn hc L v s' t' ρ hρs hρt q hk x' y' h' := by
  have hr : g ≫ hk.lift x y h = hk.lift x' y' h' := by
    apply hk.hom_ext <;> simp only [Category.assoc, hk.lift_fst, hk.lift_snd, hx, hy]
  have hr' : g ≫ (hk.lift x y h ≫ ρ) = hk.lift x' y' h' ≫ ρ := by rw [← Category.assoc, hr]
  unfold CocycleLinearizationSelf.CocycleLinearization.mappedTransport
  rw [PullbackPointMorphism.pullbackPointMorphism_restrict]
  exact congrArg (PullbackPointMorphism.pullbackPointMorphism F v L x' y')
    (D.pointHom_restrict F u a t ht hn hc L _ (x ≫ v) (y ≫ v) _ _ g _ (x' ≫ v) (y' ≫ v)
      hr' (by rw [← Category.assoc, hx]) (by rw [← Category.assoc, hy]) _ _)

def CocycleLinearizationSelf.CocycleLinearization.mappedDescentData : F.DescentData (fun (_ : PUnit.{1}) => q) where
  obj _ := (F.map v.op.toLoc).toFunctor.obj L
  hom := fun {_Z} _ {_i _j} x y hx hy =>
    D.mappedTransport F u a t ht hn hc L v s' t' ρ hρs hρt q hk x y (hx.trans hy.symm)
  pullHom_hom := fun {_Z' _Z} g _ _ _ {_i _j} x y hx hy x' y' hx' hy' =>
    D.mappedTransport_restrict F u a t ht hn hc L v s' t' ρ hρs hρt q hk x y
      (hx.trans hy.symm) g x' y' hx' hy' _
  hom_self := fun {_Z} _ {_i} x _ => D.mappedTransport_self F u a t ht hn hc L v s' t' ρ hρs hρt q hk x
  hom_comp := fun {_Z} _ {_i _j _k} x y z hx hy hz =>
    D.mappedTransport_trans F u a t ht hn hc L v s' t' ρ hρs hρt q hk x y z
      (hx.trans hy.symm) (hy.trans hz.symm)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
