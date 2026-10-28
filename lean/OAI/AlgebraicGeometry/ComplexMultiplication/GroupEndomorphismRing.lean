import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Ring.Defs

/-! # Group Endomorphism Ring -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.GroupEndomorphismRing

noncomputable section

/-! # The actual ring of endomorphisms of a commutative group object

Addition is the group law on the target; multiplication is composition. In the category
of schemes over a field, these are algebraic group endomorphisms, rather than arbitrary
linear endomorphisms of a cohomology model.
-/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
  (X : C) [GrpObj X] [IsCommMonObj X]

/-- Algebraic group endomorphisms, written additively for their pointwise group law. -/
def GroupEndomorphism := Additive (Grp.mk X ⟶ Grp.mk X)

instance CMGroupEndomorphismRing.localInstance1 : AddCommGroup (GroupEndomorphism X) :=
  inferInstanceAs (AddCommGroup (Additive (Grp.mk X ⟶ Grp.mk X)))

/-- The endomorphism ring has the actual pointwise group sum and ordinary composition. -/
instance groupEndomorphismRing : _root_.Ring (GroupEndomorphism X) where
  toAddCommGroup := inferInstance
  mul f g := Additive.ofMul (g.toMul ≫ f.toMul)
  one := Additive.ofMul (𝟙 (Grp.mk X))
  mul_assoc f g h := congrArg Additive.ofMul (Category.assoc h.toMul g.toMul f.toMul).symm
  one_mul f := congrArg Additive.ofMul (Category.comp_id f.toMul)
  mul_one f := congrArg Additive.ofMul (Category.id_comp f.toMul)
  left_distrib f g h := congrArg Additive.ofMul (MonObj.mul_comp g.toMul h.toMul f.toMul)
  right_distrib f g h := congrArg Additive.ofMul (MonObj.comp_mul h.toMul f.toMul g.toMul)
  zero_mul f := congrArg Additive.ofMul (MonObj.comp_one f.toMul)
  mul_zero f := congrArg Additive.ofMul (MonObj.one_comp f.toMul)

/-- The underlying group homomorphism remains an actual morphism of the ambient category. -/
def GroupEndomorphism.toHom (f : GroupEndomorphism X) : X ⟶ X := f.toMul.hom.hom

instance CMGroupEndomorphismRing.localInstance2 (f : GroupEndomorphism X) : IsMonHom (GroupEndomorphism.toHom X f) :=
  f.toMul.hom.isMonHom_hom

end

end OAI.AlgebraicGeometry.ComplexMultiplication.GroupEndomorphismRing
