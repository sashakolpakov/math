import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

/-! # Scalar Graded Cup Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupData

noncomputable section

/-! Assemble the actual scalar-extended cup algebra before specializing
its coefficient modules or geometric source. -/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

universe u v w

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  (H : ℕ → Type w) [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
  (μ : ∀ i j, H i →ₗ[R] H j →ₗ[R] H (i + j)) (one : H 0)
  (hleft : ∀ i (x : S ⊗[R] H i), GradedCupTransport.degreeCast S (fun i => S ⊗[R] H i) (Nat.zero_add i)
    (BilinearScalarExtension.map S (μ 0 i) ((1 : S) ⊗ₜ[R] one) x) = x)
  (hright : ∀ i (x : S ⊗[R] H i), BilinearScalarExtension.map S (μ i 0) x ((1 : S) ⊗ₜ[R] one) = x)
  (hassoc : ∀ i j k (x : S ⊗[R] H i) (y : S ⊗[R] H j) (z : S ⊗[R] H k),
    GradedCupTransport.degreeCast S (fun i => S ⊗[R] H i) (Nat.add_assoc i j k)
      (BilinearScalarExtension.map S (μ (i + j) k) (BilinearScalarExtension.map S (μ i j) x y) z) =
        BilinearScalarExtension.map S (μ i (j + k)) x (BilinearScalarExtension.map S (μ j k) y z))
  (hsquare : ∀ x : S ⊗[R] H 1, BilinearScalarExtension.map S (μ 1 1) x x = 0)

def data : GradedCupAlgebra.Data.{v, max v w} S where
  H := fun i => S ⊗[R] H i
  cup := fun i j => BilinearScalarExtension.map S (μ i j)
  one := (1 : S) ⊗ₜ[R] one
  one_cup := hleft
  cup_one := hright
  assoc := hassoc
  square_zero := hsquare

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupData
