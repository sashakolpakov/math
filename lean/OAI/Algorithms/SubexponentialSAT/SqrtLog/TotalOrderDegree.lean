import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderBasic

namespace OAI.Algorithms

/-! Additive precision degree for a shared total-order truncation. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section
open scoped BigOperators

variable {R V α : Type*} [CommSemiring R]

/-- The U^j coefficient has degree at most a+b*j in the input variables. -/
def DegreeBound (a b : ℕ) (P : Polynomial (MvPolynomial V R)) : Prop :=
  ∀ j, (P.coeff j).totalDegree ≤ a + b * j

theorem degreeBound_zero (a b : ℕ) :
    DegreeBound a b (0 : Polynomial (MvPolynomial V R)) := by
  intro j
  simp

theorem degreeBound_one (b : ℕ) :
    DegreeBound 0 b (1 : Polynomial (MvPolynomial V R)) := by
  intro j
  by_cases hj : j = 0 <;> simp [Polynomial.coeff_one, hj]

theorem degreeBound_mul {a c b : ℕ} {P Q : Polynomial (MvPolynomial V R)}
    (hP : DegreeBound a b P) (hQ : DegreeBound c b Q) :
    DegreeBound (a + c) b (P * Q) := by
  classical
  intro j
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro uv huv
  have hj := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  apply (MvPolynomial.totalDegree_mul _ _).trans
  calc
    (P.coeff uv.1).totalDegree + (Q.coeff uv.2).totalDegree
        ≤ (a + b * uv.1) + (c + b * uv.2) := Nat.add_le_add (hP _) (hQ _)
    _ = a + c + b * j := by rw [← hj]; ring

theorem degreeBound_prod (s : Finset α) (a : α → ℕ) (b : ℕ)
    (P : α → Polynomial (MvPolynomial V R))
    (hP : ∀ i ∈ s, DegreeBound (a i) b (P i)) :
    DegreeBound (∑ i ∈ s, a i) b (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using degreeBound_one (V := V) (R := R) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact degreeBound_mul (hP i (Finset.mem_insert_self i s))
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem degreeBound_row (t a b : ℕ) (e : ℕ → MvPolynomial V R)
    (h : MvPolynomial V R) (he : ∀ j < t, (e j).totalDegree ≤ a)
    (hh : h.totalDegree ≤ b) : DegreeBound a b (row t e h) := by
  intro j
  rw [coeff_row]
  split_ifs with hj
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    apply Nat.add_le_add (he j hj)
    exact (MvPolynomial.totalDegree_pow h j).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left j hh)
  · simp

theorem degreeBound_fullProduct (s : Finset α) (t b : ℕ) (a : α → ℕ)
    (e : α → ℕ → MvPolynomial V R) (h : α → MvPolynomial V R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).totalDegree ≤ a i)
    (hh : ∀ i ∈ s, (h i).totalDegree ≤ b) :
    DegreeBound (∑ i ∈ s, a i) b (fullProduct s t e h) := by
  apply degreeBound_prod
  intro i hi
  exact degreeBound_row t (a i) b (e i) (h i) (he i hi) (hh i hi)

/-- Only the shared total U-order contributes to the precision degree. -/
theorem output_totalDegree_le (s : Finset α) (t b : ℕ) (a : α → ℕ)
    (e : α → ℕ → MvPolynomial V R) (h : α → MvPolynomial V R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).totalDegree ≤ a i)
    (hh : ∀ i ∈ s, (h i).totalDegree ≤ b) :
    (output s t e h).totalDegree ≤ (∑ i ∈ s, a i) + b * (t - 1) := by
  classical
  rw [output_eq_sum_coeff]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (degreeBound_fullProduct s t b a e h he hh j).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have := Finset.mem_range.mp hj
  omega

/-- Uniform e_s degree p-1 and H degree p yield the desired additive bound. -/
theorem output_totalDegree_prime_bound (s : Finset α) (t p : ℕ)
    (e : α → ℕ → MvPolynomial V R) (h : α → MvPolynomial V R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).totalDegree ≤ p - 1)
    (hh : ∀ i ∈ s, (h i).totalDegree ≤ p) :
    (output s t e h).totalDegree ≤ s.card * (p - 1) + p * (t - 1) := by
  simpa using output_totalDegree_le s t p (fun _ => p - 1) e h he hh

/-- After substituting degree-k hashes, both contributions scale by k. -/
theorem output_totalDegree_hash_bound (s : Finset α) (t p k : ℕ)
    (e : α → ℕ → MvPolynomial V R) (h : α → MvPolynomial V R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).totalDegree ≤ k * (p - 1))
    (hh : ∀ i ∈ s, (h i).totalDegree ≤ k * p) :
    (output s t e h).totalDegree ≤ k * (s.card * (p - 1) + p * (t - 1)) := by
  have hbound := output_totalDegree_le s t (k * p) (fun _ => k * (p - 1)) e h he hh
  calc
    _ ≤ (∑ i ∈ s, k * (p - 1)) + k * p * (t - 1) := hbound
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]; ring

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
