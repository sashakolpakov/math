import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport

/-! # Graded Cup Detection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupDetection

noncomputable section

/-! Cup identities detected by a jointly injective family of genuine
degreewise cohomology maps. -/

open OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport

universe u v w z

variable (R : Type u) [CommRing R] (H : ℕ → Type v)
  [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
  {ι : Type z} (G : ι → ℕ → Type w)
  [∀ n i, AddCommGroup (G n i)] [∀ n i, Module R (G n i)]
  (f : ∀ n i, H i →ₗ[R] G n i)
  (hf : ∀ i {x y : H i}, (∀ n, f n i x = f n i y) → x = y)
  (μ : ∀ i j, H i →ₗ[R] H j →ₗ[R] H (i + j))
  (ν : ∀ n i j, G n i →ₗ[R] G n j →ₗ[R] G n (i + j))
  (hμ : ∀ n i j x y, f n (i + j) (μ i j x y) = ν n i j (f n i x) (f n j y))

include hf hμ in
theorem assoc (hν : ∀ n i j k (x : G n i) (y : G n j) (z : G n k),
    GradedCupTransport.degreeCast R (G n) (Nat.add_assoc i j k) (ν n (i + j) k (ν n i j x y) z) =
      ν n i (j + k) x (ν n j k y z))
    (i j k : ℕ) (x : H i) (y : H j) (z : H k) :
    GradedCupTransport.degreeCast R H (Nat.add_assoc i j k) (μ (i + j) k (μ i j x y) z) =
      μ i (j + k) x (μ j k y z) := by
  apply hf (i + (j + k))
  intro n
  have hc := GradedCupTransport.degreeCast_map R H (G n) (f n) (Nat.add_assoc i j k)
    (μ (i + j) k (μ i j x y) z)
  refine hc.symm.trans ?_
  rw [hμ, hμ, hμ, hμ]
  exact hν n i j k (f n i x) (f n j y) (f n k z)

include hf hμ in
theorem one_add_swap (hν : ∀ n (x y : G n 1), ν n 1 1 x y + ν n 1 1 y x = 0)
    (x y : H 1) : μ 1 1 x y + μ 1 1 y x = 0 := by
  apply hf 2
  intro n
  rw [map_add, hμ n 1 1, hμ n 1 1, map_zero]
  exact hν n (f n 1 x) (f n 1 y)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupDetection
