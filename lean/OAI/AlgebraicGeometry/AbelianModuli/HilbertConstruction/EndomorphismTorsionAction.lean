import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismPointAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EndomorphismScalars

/-! # Endomorphism Torsion Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Endomorphisms preserve torsion and act on it through a ring homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.endRingTorsionMap (n : ℕ) (T : Over S) (f : A.EndRing) :
    A.torsionPoints n T →* A.torsionPoints n T where
  toFun x := ⟨x.val ≫ f.toMul.hom.hom, by
    change (x.val ≫ f.toMul.hom.hom) ^ n = 1
    have hx : x.val ^ n = 1 := x.property
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]⟩
  map_one' := Subtype.ext (MonObj.one_comp f.toMul.hom.hom)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x.val y.val f.toMul.hom.hom)

def Abelian.Schemes.AbelianScheme.endRingTorsionAction (n : ℕ) (T : Over S) :
    A.EndRing →+* AddMonoid.End (Additive (A.torsionPoints n T)) where
  toFun f := (A.endRingTorsionMap n T f).toAdditive
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (Subtype.ext (Category.comp_id x.toMul.val))
  map_mul' f k := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (Subtype.ext
      (Category.assoc x.toMul.val k.toMul.hom.hom f.toMul.hom.hom).symm)
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (Subtype.ext (MonObj.comp_one x.toMul.val))
  map_add' f k := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (Subtype.ext
      (MonObj.comp_mul x.toMul.val f.toMul.hom.hom k.toMul.hom.hom))

theorem Abelian.Schemes.AbelianScheme.endRingTorsionAction_natCast_self (n : ℕ) (T : Over S) :
    A.endRingTorsionAction n T (n : A.EndRing) = 0 := by
  apply AddMonoidHom.ext
  intro x
  apply congrArg Additive.ofMul
  apply Subtype.ext
  exact (A.endRing_natCast_comp T x.toMul.val n).trans x.toMul.property

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
