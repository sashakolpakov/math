import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderArray
import OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrderDegree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTernary

namespace OAI.Algorithms

/-! Integration with the constructed ternary idempotent coefficient family. -/
namespace SubexponentialSAT.SqrtLog.TotalOrder

noncomputable section
open scoped BigOperators
open SubexponentialSAT.SqrtLog.Idempotent

variable {A O K V : Type*} [CommRing A] [CommRing O] [CommRing K]

/-- Evaluation of the already constructed coefficient family. -/
def indicatorCoefficients (φ : A →+* O) (u : A) (t : ℕ) (x : O) : CoeffArray O t :=
  fun s => (Idempotent.coefficients u t s).eval₂ φ x

def indicatorRow (φ : A →+* O) (u : A) (t : ℕ) (x : O) : CoeffArray O t :=
  rowArray (indicatorCoefficients φ u t x) ((ternaryH : Polynomial A).eval₂ φ x)

theorem eval_ternaryH_dvd (φ : A →+* O) (ρ : O →+* K) (q : O)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (x : O)
    (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    q ∣ (ternaryH : Polynomial A).eval₂ φ x := by
  apply hker
  rw [eval_ternaryH]
  simp only [map_mul, map_sub, map_one, Idempotent.map_two]
  rcases hx with h | h | h <;> rw [h] <;> ring

theorem sum_indicatorRow [DecidableEq K] (φ : A →+* O) (ρ : O →+* K)
    (u : A) (hu : 2 * u = 1) (q : O) (t : ℕ)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (x : O) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    sumArray (indicatorRow φ u t x) = if ρ x = 0 then 1 else 0 := by
  exact coefficients_indicator φ ρ u hu q t hker hq x hx

/-- An array convolution of all evaluated local idempotents computes the
product of their exact residue-zero indicators, with one shared cutoff. -/
theorem sum_product_indicatorRows [DecidableEq K] (φ : A →+* O) (ρ : O →+* K)
    (u : A) (hu : 2 * u = 1) (q : O) (t : ℕ)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (xs : List O) (hx : ∀ x ∈ xs, ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    sumArray (productArray (xs.map (indicatorRow φ u t))) =
      (xs.map (fun x => if ρ x = 0 then (1 : O) else 0)).prod := by
  have hp : ∀ a ∈ xs.map (indicatorRow φ u t),
      SubexponentialSAT.NilpotentDefect.PowerDivisible q (asPolynomial a) := by
    intro a ha
    obtain ⟨x, hxmem, rfl⟩ := List.mem_map.mp ha
    exact powerDivisible_rowArray q _ _ (eval_ternaryH_dvd φ ρ q hker x (hx x hxmem))
  rw [sum_productArray_of_powerDivisible q _ hp hq, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro x hxmem
  exact sum_indicatorRow φ ρ u hu q t hker hq x (hx x hxmem)

/-- Degree of a univariate polynomial after substitution into a degree-k hash. -/
theorem eval₂_totalDegree_le (P : Polynomial A) (F : MvPolynomial V A)
    (k : ℕ) (hF : F.totalDegree ≤ k) :
    (P.eval₂ MvPolynomial.C F).totalDegree ≤ P.natDegree * k := by
  classical
  rw [Polynomial.eval₂_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_pow F j).trans
  exact Nat.mul_le_mul (by have := Finset.mem_range.mp hj; omega) hF

/-- The actual constructed e_s have degree at most 2k after substitution. -/
theorem indicatorCoefficient_degree [Nontrivial A] (u : A) (t : ℕ) (s : Fin t)
    (F : MvPolynomial V A) (k : ℕ) (hF : F.totalDegree ≤ k) :
    ((Idempotent.coefficients u t s).eval₂ MvPolynomial.C F).totalDegree ≤ k * 2 := by
  apply (eval₂_totalDegree_le _ F k hF).trans
  have hs : (Idempotent.coefficients u t s).natDegree ≤ 2 := by
    have := coefficients_degree u t s
    omega
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right k hs

theorem indicatorH_degree [Nontrivial A] (F : MvPolynomial V A)
    (k : ℕ) (hF : F.totalDegree ≤ k) :
    ((ternaryH : Polynomial A).eval₂ MvPolynomial.C F).totalDegree ≤ k * 3 := by
  simpa [ternaryH_natDegree, Nat.mul_comm] using
    eval₂_totalDegree_le (ternaryH : Polynomial A) F k hF

/-- The canonical symbolic polynomial for a finite family of actual hashes. -/
def hashOutput {α : Type*} (s : Finset α) (u : A) (t : ℕ)
    (L : α → MvPolynomial V A) : MvPolynomial V A :=
  output s t (fun i => arrayCoeff (indicatorCoefficients MvPolynomial.C u t (L i)))
    (fun i => (ternaryH : Polynomial A).eval₂ MvPolynomial.C (L i))

theorem hashOutput_degree {α : Type*} [Nontrivial A] (s : Finset α) (u : A)
    (t k : ℕ) (L : α → MvPolynomial V A)
    (hL : ∀ i ∈ s, (L i).totalDegree ≤ k) :
    (hashOutput s u t L).totalDegree ≤ k * (2 * s.card + 3 * (t - 1)) := by
  have he : ∀ i ∈ s, ∀ j < t,
      (arrayCoeff (indicatorCoefficients MvPolynomial.C u t (L i)) j).totalDegree ≤ k * (3 - 1) := by
    intro i hi j hj
    simpa only [arrayCoeff_lt _ hj, indicatorCoefficients] using
      indicatorCoefficient_degree u t ⟨j, hj⟩ (L i) k (hL i hi)
  have hh : ∀ i ∈ s,
      ((ternaryH : Polynomial A).eval₂ MvPolynomial.C (L i)).totalDegree ≤ k * 3 := by
    intro i hi
    exact indicatorH_degree (L i) k (hL i hi)
  exact (output_totalDegree_hash_bound s t 3 k _ _ he hh).trans_eq (by
    simp only [show 3 - 1 = 2 from rfl]
    ring)

theorem eval_mv_univariate (P : Polynomial A) (F : MvPolynomial V A) (x : V → A) :
    MvPolynomial.eval x (P.eval₂ MvPolynomial.C F) = P.eval (MvPolynomial.eval x F) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, Polynomial.eval_add, hP, hQ]
  | monomial j a =>
    simp only [Polynomial.eval₂_monomial, map_mul, MvPolynomial.eval_C, map_pow,
      Polynomial.eval_monomial]

/-- Actual Boolean-input semantics, once every hash has a prime-subfield residue. -/
theorem hashOutput_eval {α : Type*} [DecidableEq K] (s : Finset α) (u : A)
    (hu : 2 * u = 1) (q : A) (t : ℕ) (ρ : A →+* K)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (L : α → MvPolynomial V A) (x : V → A)
    (hL : ∀ i ∈ s, ρ (MvPolynomial.eval x (L i)) = 0 ∨
      ρ (MvPolynomial.eval x (L i)) = 1 ∨ ρ (MvPolynomial.eval x (L i)) = 2) :
    MvPolynomial.eval x (hashOutput s u t L) =
      ∏ i ∈ s, if ρ (MvPolynomial.eval x (L i)) = 0 then (1 : A) else 0 := by
  unfold hashOutput
  rw [map_output_eq_prod (MvPolynomial.eval x) q s t _ _ ?_ hq]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [arrayCoeff_lt _ (Fin.isLt _), indicatorCoefficients, eval_mv_univariate]
    exact coefficients_indicator (RingHom.id A) ρ u hu q t hker hq
      (MvPolynomial.eval x (L i)) (hL i hi)
  · intro i hi
    rw [eval_mv_univariate]
    exact eval_ternaryH_dvd (RingHom.id A) ρ q hker _ (hL i hi)

end
end SubexponentialSAT.SqrtLog.TotalOrder

end OAI.Algorithms
