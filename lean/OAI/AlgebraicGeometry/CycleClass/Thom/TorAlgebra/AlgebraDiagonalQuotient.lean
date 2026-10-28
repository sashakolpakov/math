import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalModule
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Algebra Diagonal Quotient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AlgebraDiagonalQuotient

noncomputable section

/-! The actual multiplication module is the quotient by the kernel
of tensor multiplication. The comparison preserves the tensor algebra
action, not only the underlying additive groups. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DiagonalModule

universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]

def diagonalIdeal : Ideal (R ⊗[k] R) :=
  RingHom.ker (Algebra.TensorProduct.lmul' k (S := R)).toRingHom

theorem multiplication_surjective :
    Function.Surjective (Algebra.TensorProduct.lmul' k (S := R)).toRingHom := by
  intro r
  exact ⟨r ⊗ₜ[k] 1, mul_one r⟩

def diagonalQuotientEquiv :
    ((R ⊗[k] R) ⧸ diagonalIdeal k R) ≃ₗ[R ⊗[k] R] DiagonalModule.diagonalModule k R where
  __ := ((Algebra.TensorProduct.lmul' k (S := R)).toRingHom.quotientKerEquivOfSurjective
    (multiplication_surjective k R)).toAddEquiv
  map_smul' a x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Algebra.TensorProduct.lmul' k (S := R)).toRingHom.quotientKerEquivOfSurjective
      (multiplication_surjective k R) (Ideal.Quotient.mk _ (a * x)) =
      Algebra.TensorProduct.lmul' k a *
        (Algebra.TensorProduct.lmul' k (S := R)).toRingHom.quotientKerEquivOfSurjective
          (multiplication_surjective k R) (Ideal.Quotient.mk _ x)
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk, map_mul]
    rfl

def diagonalQuotientIso : ModuleCat.of (R ⊗[k] R) ((R ⊗[k] R) ⧸ diagonalIdeal k R) ≅
    DiagonalModule.diagonalModule k R := (diagonalQuotientEquiv k R).toModuleIso

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.AlgebraDiagonalQuotient
