import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CharacteristicPolynomial
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! # Prime To Evaluation -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation.IntegerComparison

/-! Common integer values determine a common rational polynomial. If the
coefficients in one realization are integral over the integers, the common
polynomial has integer coefficients. These are algebraic reconstruction
lemmas; the shared evaluation identities remain explicit hypotheses. -/

open _root_.Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]

/-- Rational interpolation at consecutive integers starting at `b`. -/
def interpolation (b d : ℕ) (values : ℕ → ℤ) : Polynomial ℚ :=
  Lagrange.interpolate (Finset.range (d + 1))
    (fun i : ℕ => ((b + i : ℕ) : ℚ)) (fun i => (values (b + i) : ℚ))

theorem nodes_injective (F : Type*) [Field F] [CharZero F] (b : ℕ) :
    Function.Injective (fun i : ℕ => ((b + i : ℕ) : F)) := by
  intro i j h
  exact Nat.add_left_cancel ((Nat.cast_injective (R := F)) h)

/-- A polynomial of degree at most `d` is recovered from `d + 1` shared
integer values, independently of the characteristic-zero coefficient field. -/
theorem eq_map_interpolation (P : Polynomial K) (b d : ℕ) (values : ℕ → ℤ)
    (hdegree : P.natDegree ≤ d)
    (hvalues : ∀ i : ℕ, i ≤ d → P.eval ((b + i : ℕ) : K) = values (b + i)) :
    P = (interpolation b d values).map (algebraMap ℚ K) := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (Finset.range (d + 1))
    (nodes_injective K b).injOn
  · rw [Finset.card_range]
    exact P.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hdegree)
  · exact Polynomial.degree_map_le.trans_lt
      (Lagrange.degree_interpolate_lt _ (nodes_injective ℚ b).injOn)
  · intro i hi
    have hi' : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have he := Lagrange.eval_interpolate_at_node
      (fun j : ℕ => (values (b + j) : ℚ)) (nodes_injective ℚ b).injOn hi
    have hmap := congrArg (algebraMap ℚ K) he
    rw [hvalues i hi']
    simpa only [interpolation, ← Polynomial.eval_map_apply, map_natCast, map_intCast] using hmap.symm

/-- Agreement with a common integer-valued function on a tail of the
natural numbers produces one polynomial over the rationals. -/
theorem exists_common_rational (P : Polynomial K) (Q : Polynomial L)
    (b : ℕ) (values : ℕ → ℤ)
    (hP : ∀ n : ℕ, b ≤ n → P.eval (n : K) = values n)
    (hQ : ∀ n : ℕ, b ≤ n → Q.eval (n : L) = values n) :
    ∃ R : Polynomial ℚ,
      P = R.map (algebraMap ℚ K) ∧ Q = R.map (algebraMap ℚ L) := by
  let d := max P.natDegree Q.natDegree
  refine ⟨interpolation b d values, ?_, ?_⟩
  · exact eq_map_interpolation P b d values (le_max_left _ _)
      (fun i _ => hP (b + i) (Nat.le_add_right b i))
  · exact eq_map_interpolation Q b d values (le_max_right _ _)
      (fun i _ => hQ (b + i) (Nat.le_add_right b i))

/-- Integral coefficients on one side make the common rational polynomial
integral. No integrality hypothesis on the second side is needed. -/
theorem exists_common_integer (P : Polynomial K) (Q : Polynomial L)
    (b : ℕ) (values : ℕ → ℤ)
    (hP : ∀ n : ℕ, b ≤ n → P.eval (n : K) = values n)
    (hQ : ∀ n : ℕ, b ≤ n → Q.eval (n : L) = values n)
    (hintegral : ∀ i : ℕ, IsIntegral ℤ (P.coeff i)) :
    ∃ R : Polynomial ℤ,
      P = R.map (Int.castRingHom K) ∧ Q = R.map (Int.castRingHom L) := by
  obtain ⟨R, hRK, hRL⟩ := exists_common_rational P Q b values hP hQ
  have hcoeff (i : ℕ) : IsIntegral ℤ (R.coeff i) := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := K)).mp
    simpa only [hRK, Polynomial.coeff_map] using hintegral i
  have hlift : R ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    apply (Polynomial.lifts_iff_coeff_lifts R).mpr
    intro i
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (hcoeff i)
  obtain ⟨S, hS⟩ := (Polynomial.mem_lifts R).mp hlift
  refine ⟨S, ?_, ?_⟩
  · rw [← hS, Polynomial.map_map] at hRK
    exact hRK.trans (congrArg (fun f : ℤ →+* K => S.map f) (Subsingleton.elim _ _))
  · rw [← hS, Polynomial.map_map] at hRL
    exact hRL.trans (congrArg (fun f : ℤ →+* L => S.map f) (Subsingleton.elim _ _))

/-- For integral operators, common integer characteristic-polynomial
evaluations determine a common monic integer characteristic polynomial. -/
theorem charpoly_exists_common_integer
    {V U : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup U] [Module L U] [FiniteDimensional L U]
    (F : Module.End K V) (G : Module.End L U) (hF : IsIntegral ℤ F)
    (b : ℕ) (values : ℕ → ℤ)
    (hK : ∀ n : ℕ, b ≤ n → F.charpoly.eval (n : K) = values n)
    (hL : ∀ n : ℕ, b ≤ n → G.charpoly.eval (n : L) = values n) :
    ∃ P : Polynomial ℤ, P.Monic ∧
      F.charpoly = P.map (Int.castRingHom K) ∧
      G.charpoly = P.map (Int.castRingHom L) := by
  obtain ⟨P, hP, hQ⟩ := exists_common_integer F.charpoly G.charpoly b values hK hL
    (Integral.CharacteristicPolynomial.coeff_integral F hF)
  refine ⟨P, ?_, hP, hQ⟩
  exact Polynomial.monic_of_injective (Int.cast_injective (α := K))
    (hP ▸ F.charpoly_monic)

end NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation.IntegerComparison

namespace NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation.CharacteristicPolynomial

/-! Evaluations at the prime-to-characteristic integer shifts suffice
to identify the complete characteristic polynomial, including all
root multiplicities. -/

variable {K : Type*} [Field K] [CharZero K]

def node (p b i : ℕ) : ℕ := 1 + p * (b + i)

theorem node_ge (p b i : ℕ) (hp : 0 < p) : b ≤ node p b i := by
  have h := Nat.le_mul_of_pos_left (b + i) hp
  dsimp [node]
  omega

theorem not_dvd_node (p b i : ℕ) (hp : 1 < p) : ¬p ∣ node p b i := by
  intro h
  have hmod := Nat.mod_eq_zero_of_dvd h
  have hone : 1 % p = 1 := Nat.mod_eq_of_lt hp
  simp only [node, Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, hone] at hmod
  omega

theorem nodes_injective (p b : ℕ) (hp : 0 < p) :
    Function.Injective (fun i => (node p b i : K)) := by
  intro i j h
  have he : node p b i = node p b j := Nat.cast_injective h
  have hm : p * (b + i) = p * (b + j) := Nat.add_left_cancel he
  exact Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left hp hm)

theorem eq_of_prime_to_evaluations (P Q : Polynomial K) (p b : ℕ) (hp : 1 < p)
    (h : ∀ n : ℕ, b ≤ n → ¬p ∣ n → P.eval (n : K) = Q.eval (n : K)) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite (Set.range (fun i => (node p b i : K))) :=
    Set.infinite_range_of_injective (nodes_injective p b (Nat.zero_lt_of_lt hp))
  apply hinf.mono
  rintro x ⟨i, rfl⟩
  exact h (node p b i) (node_ge p b i (Nat.zero_lt_of_lt hp)) (not_dvd_node p b i hp)

theorem eq_integer_polynomial_of_prime_to_evaluations (P : Polynomial K) (W : Polynomial ℤ)
    (p b : ℕ) (hp : 1 < p)
    (h : ∀ n : ℕ, b ≤ n → ¬p ∣ n → P.eval (n : K) = ((W.eval (n : ℤ) : ℤ) : K)) :
    P = W.map (Int.castRingHom K) := by
  apply eq_of_prime_to_evaluations P (W.map (Int.castRingHom K)) p b hp
  intro n hn hpn
  rw [h n hn hpn, Polynomial.eval_natCast_map]
  rfl

end NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation.CharacteristicPolynomial

namespace NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation.Negative

/-! Negative prime-to-characteristic integer evaluations determine the
whole polynomial, with no loss of root multiplicity. -/

open OAI.NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation.CharacteristicPolynomial

variable {K : Type*} [Field K] [CharZero K]

theorem eq_of_evaluations (P Q : Polynomial K) (p b : ℕ) (hp : 1 < p)
    (h : ∀ n : ℕ, b ≤ n → ¬p ∣ n → P.eval (-(n : K)) = Q.eval (-(n : K))) : P = Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun i => -(CharacteristicPolynomial.node p b i : K)) :=
    neg_injective.comp (CharacteristicPolynomial.nodes_injective p b (Nat.zero_lt_of_lt hp))
  have hinf : Set.Infinite (Set.range (fun i => -(CharacteristicPolynomial.node p b i : K))) :=
    Set.infinite_range_of_injective hinj
  apply hinf.mono
  rintro x ⟨i, rfl⟩
  exact h (CharacteristicPolynomial.node p b i) (CharacteristicPolynomial.node_ge p b i (Nat.zero_lt_of_lt hp)) (CharacteristicPolynomial.not_dvd_node p b i hp)

theorem eq_integer_polynomial (P : Polynomial K) (W : Polynomial ℤ)
    (p b : ℕ) (hp : 1 < p)
    (h : ∀ n : ℕ, b ≤ n → ¬p ∣ n → P.eval (-(n : K)) = ((W.eval (-(n : ℤ)) : ℤ) : K)) :
    P = W.map (Int.castRingHom K) := by
  apply eq_of_evaluations P (W.map (Int.castRingHom K)) p b hp
  intro n hn hpn
  rw [h n hn hpn]
  simpa only [Int.coe_castRingHom, Int.cast_id, Int.cast_neg, Int.cast_natCast] using
    (Polynomial.eval_intCast_map (Int.castRingHom K) W (-(n : ℤ))).symm

end NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation.Negative

end

end OAI
