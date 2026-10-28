import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupData

/-! # Scalar Graded Cup Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupProjection

noncomputable section

/-! Normalize the scalar-extended algebra fields while all coefficient
modules remain abstract. -/

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

theorem cup_apply (i j : ℕ) (x : S ⊗[R] H i) (y : S ⊗[R] H j) :
    (ScalarGradedCupData.data S H μ one hleft hright hassoc hsquare).cup i j x y =
      BilinearScalarExtension.map S (μ i j) x y := rfl

theorem cup_natural (f : ∀ n, Module.End R (H n))
    (hf : ∀ i j (x : H i) (y : H j), f (i + j) (μ i j x y) = μ i j (f i x) (f j y))
    (i j : ℕ) (x : S ⊗[R] H i) (y : S ⊗[R] H j) :
    (f (i + j)).baseChange S
        ((ScalarGradedCupData.data S H μ one hleft hright hassoc hsquare).cup i j x y) =
      (ScalarGradedCupData.data S H μ one hleft hright hassoc hsquare).cup i j
        ((f i).baseChange S x) ((f j).baseChange S y) := by
  change (f (i + j)).baseChange S (BilinearScalarExtension.map S (μ i j) x y) =
    BilinearScalarExtension.map S (μ i j) ((f i).baseChange S x) ((f j).baseChange S y)
  exact BilinearScalarExtension.map_natural S (μ i j) (μ i j) (f i) (f j) (f (i + j)) (hf i j) x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupProjection
