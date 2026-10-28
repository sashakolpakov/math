import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Endomorphisms -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction

/-!
# Completion: algebraic endomorphisms and their rational algebra

These are actual group-object morphisms, with pointwise addition and
composition as multiplication. No finiteness, polarization, or spectral
property is part of the definition.
-/

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

universe u v

section Endomorphisms

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [BraidedCategory C] (A : C) [GrpObj A] [IsCommMonObj A]

/-- Algebraic group endomorphisms, with the pointwise group law written additively. -/
abbrev AlgebraicEnd := Additive (Grp.mk A ⟶ Grp.mk A)

instance algebraicEndMonoid : Monoid (AlgebraicEnd A) where
  one := Additive.ofMul (𝟙 (Grp.mk A))
  mul f g := Additive.ofMul (g.toMul ≫ f.toMul)
  mul_assoc f g h := (Category.assoc h.toMul g.toMul f.toMul).symm
  one_mul f := Category.comp_id f.toMul
  mul_one f := Category.id_comp f.toMul

instance algebraicEndRing : Ring (AlgebraicEnd A) :=
  { algebraicEndMonoid A, (inferInstance : AddCommGroup (AlgebraicEnd A)) with
    zero_mul := fun f => MonObj.comp_one f.toMul
    mul_zero := fun f => MonObj.one_comp f.toMul
    left_distrib := fun f g h => MonObj.mul_comp g.toMul h.toMul f.toMul
    right_distrib := fun f g h => MonObj.comp_mul h.toMul f.toMul g.toMul }

/-- The rational algebra of actual algebraic group endomorphisms. -/
abbrev RationalAlgebraicEnd := TensorProduct ℤ ℚ (AlgebraicEnd A)

theorem algebraicEnd_mul_apply (f g : AlgebraicEnd A) :
    (f * g).toMul.hom.hom = g.toMul.hom.hom ≫ f.toMul.hom.hom := rfl

end Endomorphisms

open _root_.AlgebraicGeometry

variable (k : Type u) [Field k] [Fintype k]
    (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

/-- Frobenius as an element of the genuine endomorphism ring. -/
noncomputable def algebraicFrobenius : AlgebraicEnd A :=
  Additive.ofMul (Grp.ofHom (Frobenius.Construction.finiteFieldSchemeFrobenius k A))

/-- Frobenius in the rationalized endomorphism algebra. -/
noncomputable def rationalAlgebraicFrobenius : RationalAlgebraicEnd A :=
  (1 : ℚ) ⊗ₜ[ℤ] algebraicFrobenius k A

/-- Frobenius commutes with every endomorphism defined over the ground field. -/
theorem algebraicFrobenius_commutes (f : AlgebraicEnd A) :
    Commute (algebraicFrobenius k A) f := by
  change f.toMul ≫ (algebraicFrobenius k A).toMul =
    (algebraicFrobenius k A).toMul ≫ f.toMul
  apply Grp.hom_ext
  exact (Frobenius.Construction.finiteFieldSchemeFrobenius_naturality k A f.toMul.hom.hom).symm

/-- The rational Frobenius element lies in the center of End⁰ over k. -/
theorem rationalAlgebraicFrobenius_commutes (x : RationalAlgebraicEnd A) :
    Commute (rationalAlgebraicFrobenius k A) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r f =>
    change ((1 : ℚ) ⊗ₜ[ℤ] algebraicFrobenius k A) * (r ⊗ₜ[ℤ] f) =
      (r ⊗ₜ[ℤ] f) * ((1 : ℚ) ⊗ₜ[ℤ] algebraicFrobenius k A)
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
    rw [(algebraicFrobenius_commutes k A f).eq]
  | add x y hx hy => exact hx.add_right hy

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction
