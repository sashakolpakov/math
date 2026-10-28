import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentObjectIso

/-! # Quotient Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.QuotientTransport

noncomputable section

/-!
# Ordinary descent data as transport between two points of the same quotient fiber
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  {A B : C} (f : A ⟶ B) (D : F.DescentData (fun (_ : PUnit.{1}) => f))

/-- The actual ordinary gluing isomorphism between two test points in one quotient fiber. -/
def transport {T : C} (x y : T ⟶ A) (h : x ≫ f = y ≫ f) :
    (F.map x.op.toLoc).toFunctor.obj (D.obj PUnit.unit) ⟶
      (F.map y.op.toLoc).toFunctor.obj (D.obj PUnit.unit) :=
  (D.iso (x ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y rfl h.symm).hom

/-- The original diagonal identity gives identity quotient transport. -/
theorem transport_self {T : C} (x : T ⟶ A) (h : x ≫ f = x ≫ f) : transport f D x x h = 𝟙 _ :=
  D.hom_self (x ≫ f) (i := PUnit.unit) x rfl

/-- The original cocycle composes quotient transports with their independently presented base points. -/
theorem transport_comp {T : C} (x y z : T ⟶ A) (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f)
    (hxz : x ≫ f = z ≫ f) : transport f D x y hxy ≫ transport f D y z hyz = transport f D x z hxz :=
  PullHom.descentIso_comp f D x y z hxy hyz

/-- Ordinary quotient transport has its full native change-of-test-object law. -/
theorem transport_pullback {T T' : C} (g : T' ⟶ T) (x y : T ⟶ A) (h : x ≫ f = y ≫ f)
    (x' y' : T' ⟶ A) (h' : x' ≫ f = y' ≫ f) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    pullHom (transport f D x y h) g x' y' hx hy = transport f D x' y' h' := by
  have hq : g ≫ (x ≫ f) = x' ≫ f := (Category.assoc g x f).symm.trans
    (congrArg (fun a => a ≫ f) hx)
  exact D.pullHom_hom g (x ≫ f) (x' ≫ f) hq (i₁ := PUnit.unit) (i₂ := PUnit.unit)
    x y rfl h.symm x' y' hx hy

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.QuotientTransport
