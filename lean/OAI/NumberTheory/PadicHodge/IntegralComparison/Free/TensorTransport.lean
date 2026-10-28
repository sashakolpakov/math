import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CompatibleAlgebraEquiv

/-! # Tensor Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.TensorTransport

noncomputable section

/-! Freeness of scalar extension is independent of the chosen
isomorphic coefficient algebra. -/

open scoped TensorProduct

attribute [local instance] PeriodInvariants.SemilinearScalarFactorization.forwardPair
  PeriodInvariants.SemilinearScalarFactorization.backwardPair

universe u

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] (e : C ≃ₐ[A] D)

def equiv : C ⊗[A] B ≃ₛₗ[e.toRingEquiv.toRingHom] D ⊗[A] B where
  __ := (Algebra.TensorProduct.congr e (AlgEquiv.refl : B ≃ₐ[A] B)).toAddEquiv
  map_smul' c z := by
    change (Algebra.TensorProduct.congr e (AlgEquiv.refl : B ≃ₐ[A] B)) (c • z) =
      e c • (Algebra.TensorProduct.congr e (AlgEquiv.refl : B ≃ₐ[A] B)) z
    simp only [Algebra.smul_def, map_mul]
    congr 1

include e in
theorem free [Module.Free C (C ⊗[A] B)] : Module.Free D (D ⊗[A] B) :=
  Module.Free.of_equiv (equiv (B := B) e)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.TensorTransport
