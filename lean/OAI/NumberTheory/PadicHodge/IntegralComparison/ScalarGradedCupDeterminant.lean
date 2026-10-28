import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupProjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedExteriorCup

/-! # Scalar Graded Cup Determinant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupDeterminant

noncomputable section

/-! The determinant identity for a scalar-extended graded cup algebra,
proved before specializing its coefficient modules. -/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

universe u v w

variable {R : Type u} [CommRing R] (S : Type v) [Field S] [Algebra R S]
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
  [FiniteDimensional S (S ⊗[R] H 1)]
  (f : ∀ n, Module.End R (H n))
  (hunit : (f 0).baseChange S ((1 : S) ⊗ₜ[R] one) = (1 : S) ⊗ₜ[R] one)
  (hf : ∀ i j (x : H i) (y : H j), f (i + j) (μ i j x y) = μ i j (f i x) (f j y))

local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupData.data S H μ one hleft hright hassoc hsquare
local notation "N" => Module.finrank S (S ⊗[R] H 1)

include hunit hf in
theorem det_eq_of_top_scalar (c : S)
    (hprod : GradedExteriorCup.exteriorPowerCup D N ≠ 0)
    (htop : ∀ x : S ⊗[R] H N, (f N).baseChange S x = c • x) :
    ((f 1).baseChange S).det = c := by
  let : FiniteDimensional S ((D).H 1) := inferInstanceAs (FiniteDimensional S (S ⊗[R] H 1))
  exact GradedExteriorCup.det_eq_of_top_scalar D (fun n => (f n).baseChange S) hunit
    (ScalarGradedCupProjection.cup_natural S H μ one hleft hright hassoc hsquare f hf)
    c hprod htop

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupDeterminant
