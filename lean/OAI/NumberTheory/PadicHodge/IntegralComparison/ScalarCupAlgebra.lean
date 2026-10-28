import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

/-! # Scalar Cup Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarCupAlgebra

noncomputable section

/-! Associativity and degree-one anticommutativity persist under
scalar extension of a graded bilinear cup product. -/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearScalarExtension

universe u v w

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  (H : ℕ → Type w) [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]

theorem degreeCast_tmul {m n : ℕ} (h : m = n) (a : S) (x : H m) :
    GradedCupTransport.degreeCast S (fun i => S ⊗[R] H i) h (a ⊗ₜ[R] x) =
      a ⊗ₜ[R] GradedCupTransport.degreeCast R H h x := by
  subst n
  rfl

theorem degreeCast_changeRing (T : Type*) [CommRing T] [∀ i, Module T (H i)]
    {m n : ℕ} (h : m = n) (x : H m) : GradedCupTransport.degreeCast T H h x = GradedCupTransport.degreeCast R H h x := by
  subst n
  rfl

variable (μ : ∀ i j, H i →ₗ[R] H j →ₗ[R] H (i + j))

theorem assoc (hμ : ∀ i j k (x : H i) (y : H j) (z : H k),
    GradedCupTransport.degreeCast R H (Nat.add_assoc i j k) (μ (i + j) k (μ i j x y) z) = μ i (j + k) x (μ j k y z))
    (i j k : ℕ) (x : S ⊗[R] H i) (y : S ⊗[R] H j) (z : S ⊗[R] H k) :
    GradedCupTransport.degreeCast S (fun i => S ⊗[R] H i) (Nat.add_assoc i j k)
      (BilinearScalarExtension.map S (μ (i + j) k) (BilinearScalarExtension.map S (μ i j) x y) z) =
      BilinearScalarExtension.map S (μ i (j + k)) x (BilinearScalarExtension.map S (μ j k) y z) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | tmul b y =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | tmul c z => rw [BilinearScalarExtension.map_tmul, BilinearScalarExtension.map_tmul, BilinearScalarExtension.map_tmul, BilinearScalarExtension.map_tmul, degreeCast_tmul, hμ, mul_assoc]

theorem one_add_swap (hμ : ∀ x y : H 1, μ 1 1 x y + μ 1 1 y x = 0)
    (x y : S ⊗[R] H 1) : BilinearScalarExtension.map S (μ 1 1) x y + BilinearScalarExtension.map S (μ 1 1) y x = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply]
    calc
      _ = (BilinearScalarExtension.map S (μ 1 1) x y + BilinearScalarExtension.map S (μ 1 1) y x) +
          (BilinearScalarExtension.map S (μ 1 1) z y + BilinearScalarExtension.map S (μ 1 1) y z) := by abel
      _ = 0 := by rw [hx, hz, add_zero]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      simp only [map_add, LinearMap.add_apply]
      calc
        _ = (BilinearScalarExtension.map S (μ 1 1) (a ⊗ₜ[R] x) y + BilinearScalarExtension.map S (μ 1 1) y (a ⊗ₜ[R] x)) +
            (BilinearScalarExtension.map S (μ 1 1) (a ⊗ₜ[R] x) z + BilinearScalarExtension.map S (μ 1 1) z (a ⊗ₜ[R] x)) := by abel
        _ = 0 := by rw [hy, hz, add_zero]
    | tmul b y => rw [BilinearScalarExtension.map_tmul, BilinearScalarExtension.map_tmul, mul_comm b a, ← TensorProduct.tmul_add, hμ,
        TensorProduct.tmul_zero]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarCupAlgebra
