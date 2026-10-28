import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderBasic

namespace OAI.Algorithms

/-! The same additive bound for ordinary polynomial degree, e.g. the CRT path T. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section
open scoped BigOperators

variable {R α : Type*} [CommSemiring R]

/-- The U^j coefficient has degree at most a+b*j in the input variables. -/
def PathDegreeBound (a b : ℕ) (P : Polynomial (Polynomial R)) : Prop :=
  ∀ j, (P.coeff j).natDegree ≤ a + b * j

theorem pathDegreeBound_zero (a b : ℕ) :
    PathDegreeBound a b (0 : Polynomial (Polynomial R)) := by
  intro j
  simp

theorem pathDegreeBound_one (b : ℕ) :
    PathDegreeBound 0 b (1 : Polynomial (Polynomial R)) := by
  intro j
  by_cases hj : j = 0 <;> simp [Polynomial.coeff_one, hj]

theorem pathDegreeBound_mul {a c b : ℕ} {P Q : Polynomial (Polynomial R)}
    (hP : PathDegreeBound a b P) (hQ : PathDegreeBound c b Q) :
    PathDegreeBound (a + c) b (P * Q) := by
  classical
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le _ _
  intro uv huv
  have hj := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  apply (Polynomial.natDegree_mul_le).trans
  calc
    (P.coeff uv.1).natDegree + (Q.coeff uv.2).natDegree
        ≤ (a + b * uv.1) + (c + b * uv.2) := Nat.add_le_add (hP _) (hQ _)
    _ = a + c + b * j := by rw [← hj]; ring

theorem pathDegreeBound_prod (s : Finset α) (a : α → ℕ) (b : ℕ)
    (P : α → Polynomial (Polynomial R))
    (hP : ∀ i ∈ s, PathDegreeBound (a i) b (P i)) :
    PathDegreeBound (∑ i ∈ s, a i) b (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pathDegreeBound_one (R := R) b
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact pathDegreeBound_mul (hP i (Finset.mem_insert_self i s))
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem pathDegreeBound_row (t a b : ℕ) (e : ℕ → Polynomial R)
    (h : Polynomial R) (he : ∀ j < t, (e j).natDegree ≤ a)
    (hh : h.natDegree ≤ b) : PathDegreeBound a b (row t e h) := by
  intro j
  rw [coeff_row]
  split_ifs with hj
  · apply (Polynomial.natDegree_mul_le).trans
    apply Nat.add_le_add (he j hj)
    exact (Polynomial.natDegree_pow_le (p := h) (n := j)).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left j hh)
  · simp

theorem pathDegreeBound_fullProduct (s : Finset α) (t b : ℕ) (a : α → ℕ)
    (e : α → ℕ → Polynomial R) (h : α → Polynomial R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).natDegree ≤ a i)
    (hh : ∀ i ∈ s, (h i).natDegree ≤ b) :
    PathDegreeBound (∑ i ∈ s, a i) b (fullProduct s t e h) := by
  apply pathDegreeBound_prod
  intro i hi
  exact pathDegreeBound_row t (a i) b (e i) (h i) (he i hi) (hh i hi)

/-- Only the shared total U-order contributes to the precision degree. -/
theorem output_pathDegree_le (s : Finset α) (t b : ℕ) (a : α → ℕ)
    (e : α → ℕ → Polynomial R) (h : α → Polynomial R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).natDegree ≤ a i)
    (hh : ∀ i ∈ s, (h i).natDegree ≤ b) :
    (output s t e h).natDegree ≤ (∑ i ∈ s, a i) + b * (t - 1) := by
  classical
  rw [output_eq_sum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le _ _
  intro j hj
  apply (pathDegreeBound_fullProduct s t b a e h he hh j).trans
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  have := Finset.mem_range.mp hj
  omega

/-- Uniform e_s degree p-1 and H degree p yield the desired additive bound. -/
theorem output_pathDegree_prime_bound (s : Finset α) (t p : ℕ)
    (e : α → ℕ → Polynomial R) (h : α → Polynomial R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).natDegree ≤ p - 1)
    (hh : ∀ i ∈ s, (h i).natDegree ≤ p) :
    (output s t e h).natDegree ≤ s.card * (p - 1) + p * (t - 1) := by
  simpa using output_pathDegree_le s t p (fun _ => p - 1) e h he hh

/-- After substituting degree-k hashes, both contributions scale by k. -/
theorem output_pathDegree_hash_bound (s : Finset α) (t p k : ℕ)
    (e : α → ℕ → Polynomial R) (h : α → Polynomial R)
    (he : ∀ i ∈ s, ∀ j < t, (e i j).natDegree ≤ k * (p - 1))
    (hh : ∀ i ∈ s, (h i).natDegree ≤ k * p) :
    (output s t e h).natDegree ≤ k * (s.card * (p - 1) + p * (t - 1)) := by
  have hbound := output_pathDegree_le s t (k * p) (fun _ => k * (p - 1)) e h he hh
  calc
    _ ≤ (∑ i ∈ s, k * (p - 1)) + k * p * (t - 1) := hbound
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]; ring

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
