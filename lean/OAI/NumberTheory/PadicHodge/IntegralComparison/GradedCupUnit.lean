import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupDetection
import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarCupAlgebra

/-! # Graded Cup Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupUnit

noncomputable section

/-! Unit identities under degreewise equivalence, jointly injective
cohomology coordinates, and scalar extension. -/

open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport

universe u v w z

variable (R : Type u) [CommRing R] (H : ℕ → Type v)
  [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
  (G : ℕ → Type w) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (e : ∀ i, H i ≃ₗ[R] G i)
  (μ : ∀ i j, H i →ₗ[R] H j →ₗ[R] H (i + j)) (one : H 0)

theorem transported_left (h : ∀ i x, GradedCupTransport.degreeCast R H (Nat.zero_add i) (μ 0 i one x) = x)
    (i : ℕ) (x : G i) :
    GradedCupTransport.degreeCast R G (Nat.zero_add i) (GradedCupTransport.cup R H G e μ 0 i (e 0 one) x) = x := by
  obtain ⟨x, rfl⟩ := (e i).surjective x
  rw [GradedCupTransport.cup_apply]
  exact (GradedCupTransport.degreeCast_map R H G (fun n => (e n).toLinearMap) (Nat.zero_add i) _).trans
    (congrArg (e i) (h i x))

theorem transported_right (h : ∀ i x, μ i 0 x one = x) (i : ℕ) (x : G i) :
    GradedCupTransport.cup R H G e μ i 0 x (e 0 one) = x := by
  obtain ⟨x, rfl⟩ := (e i).surjective x
  rw [GradedCupTransport.cup_apply R H G e μ i 0, h]
  rfl

section Detection

variable {ι : Type z} (B : ι → ℕ → Type w)
  [∀ n i, AddCommGroup (B n i)] [∀ n i, Module R (B n i)]
  (f : ∀ n i, H i →ₗ[R] B n i)
  (hf : ∀ i {x y : H i}, (∀ n, f n i x = f n i y) → x = y)
  (ν : ∀ n i j, B n i →ₗ[R] B n j →ₗ[R] B n (i + j))
  (hμ : ∀ n i j x y, f n (i + j) (μ i j x y) = ν n i j (f n i x) (f n j y))
  (b : ∀ n, B n 0) (hb : ∀ n, f n 0 one = b n)

include hf hμ hb in
theorem detected_left (h : ∀ n i x, GradedCupTransport.degreeCast R (B n) (Nat.zero_add i) (ν n 0 i (b n) x) = x)
    (i : ℕ) (x : H i) : GradedCupTransport.degreeCast R H (Nat.zero_add i) (μ 0 i one x) = x := by
  apply hf i
  intro n
  refine (GradedCupTransport.degreeCast_map R H (B n) (f n) (Nat.zero_add i) _).symm.trans ?_
  rw [hμ n 0 i, hb, h]

include hf hμ hb in
theorem detected_right (h : ∀ n i x, ν n i 0 x (b n) = x) (i : ℕ) (x : H i) :
    μ i 0 x one = x := by
  apply hf i
  intro n
  exact (hμ n i 0 x one).trans
    ((congrArg (ν n i 0 (f n i x)) (hb n)).trans (h n i (f n i x)))

end Detection

variable (S : Type z) [CommRing S] [Algebra R S]

theorem scalar_left (h : ∀ i x, GradedCupTransport.degreeCast R H (Nat.zero_add i) (μ 0 i one x) = x)
    (i : ℕ) (x : S ⊗[R] H i) :
    GradedCupTransport.degreeCast S (fun i => S ⊗[R] H i) (Nat.zero_add i)
      (BilinearScalarExtension.map S (μ 0 i) ((1 : S) ⊗ₜ[R] one) x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rw [BilinearScalarExtension.map_tmul, ScalarCupAlgebra.degreeCast_tmul, h, one_mul]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupUnit
