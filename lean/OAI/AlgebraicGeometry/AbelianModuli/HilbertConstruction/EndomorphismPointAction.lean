import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.EndomorphismRing
import Mathlib.Algebra.Module.End

/-! # Endomorphism Point Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The endomorphism ring acts on every group of points by postcomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)

def Abelian.Schemes.AbelianScheme.endRingPointAction (T : Over S) : A.EndRing →+* AddMonoid.End (Additive (A.Points T)) where
  toFun f := {
    toFun x := Additive.ofMul (x.toMul ≫ f.toMul.hom.hom)
    map_zero' := congrArg Additive.ofMul (MonObj.one_comp f.toMul.hom.hom)
    map_add' x y := congrArg Additive.ofMul (MonObj.mul_comp x.toMul y.toMul f.toMul.hom.hom) }
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (Category.comp_id x.toMul)
  map_mul' f k := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (Category.assoc x.toMul k.toMul.hom.hom f.toMul.hom.hom).symm
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (MonObj.comp_one x.toMul)
  map_add' f k := by
    apply AddMonoidHom.ext
    intro x
    exact congrArg Additive.ofMul (MonObj.comp_mul x.toMul f.toMul.hom.hom k.toMul.hom.hom)

theorem Abelian.Schemes.AbelianScheme.endRingPointAction_injective : Function.Injective (A.endRingPointAction A.scheme) := by
  intro f k h
  have he := congrArg (fun e : AddMonoid.End (Additive (A.Points A.scheme)) =>
    (e (Additive.ofMul (𝟙 A.scheme))).toMul) h
  change (𝟙 A.scheme) ≫ f.toMul.hom.hom = (𝟙 A.scheme) ≫ k.toMul.hom.hom at he
  rw [Category.id_comp, Category.id_comp] at he
  exact congrArg Additive.ofMul (Grp.hom_ext _ _ he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
