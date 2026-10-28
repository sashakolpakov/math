import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.GroupObjects

/-! # Endomorphism Ring -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! The endomorphism ring of an abelian scheme: addition is pointwise addition and multiplication is composition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Schemes.AbelianScheme g S)

abbrev Schemes.AbelianScheme.EndRing := A.AddHom A

instance Schemes.AbelianScheme.endRingRing : _root_.Ring A.EndRing where
  toAddCommGroup := inferInstance
  mul f k := Additive.ofMul (k.toMul ≫ f.toMul)
  one := Additive.ofMul (𝟙 A.groupObject)
  mul_assoc f k l := congrArg Additive.ofMul (Category.assoc l.toMul k.toMul f.toMul).symm
  one_mul f := congrArg Additive.ofMul (Category.comp_id f.toMul)
  mul_one f := congrArg Additive.ofMul (Category.id_comp f.toMul)
  left_distrib f k l := congrArg Additive.ofMul (MonObj.mul_comp k.toMul l.toMul f.toMul)
  right_distrib f k l := congrArg Additive.ofMul (MonObj.comp_mul l.toMul f.toMul k.toMul)
  zero_mul f := congrArg Additive.ofMul (MonObj.comp_one f.toMul)
  mul_zero f := congrArg Additive.ofMul (MonObj.one_comp f.toMul)
  natCast n := n • Additive.ofMul (𝟙 A.groupObject)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n

@[simp] theorem Schemes.AbelianScheme.endRing_mul_toMul (f k : A.EndRing) :
    (f * k).toMul = k.toMul ≫ f.toMul := rfl

@[simp] theorem Schemes.AbelianScheme.endRing_one_toMul : (1 : A.EndRing).toMul = 𝟙 A.groupObject := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
