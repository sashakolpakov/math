import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Algebraic Ring Hom Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRingHomExt.CommAlgebraicRingHomExt

/-! Equality of underlying ring homomorphisms detects equality of algebra morphisms. -/

open _root_.CategoryTheory

universe u v
variable {R : Type u} [CommRing R] {A B : CommAlgCat.{v} R}

theorem eq (f g : A ⟶ B) (h : f.hom.toRingHom = g.hom.toRingHom) : f = g :=
  CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective h)

end OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRingHomExt.CommAlgebraicRingHomExt
