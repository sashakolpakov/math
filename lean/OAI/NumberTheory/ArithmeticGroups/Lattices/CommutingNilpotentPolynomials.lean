import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.ExponentialDerivative
import Mathlib.RingTheory.Nilpotent.Exp

/-! # Commuting Nilpotent Polynomials -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingNilpotentPolynomials.Construction

noncomputable section

section

/-! Finite polynomials without constant term in commuting nilpotent
operators are nilpotent. This applies to exponential derivatives. -/

variable {R : Type*} [Ring R] [Algebra ℝ R]

omit [Algebra ℝ R] in
theorem commute_two_variable_monomials (a b : R) (hc : Commute a b)
    (i j k l : ℕ) : Commute (a ^ i * b ^ j) (a ^ k * b ^ l) :=
  ((Commute.pow_pow_self a i k).mul_right (hc.pow_pow i l)).mul_left
    ((hc.symm.pow_pow j k).mul_right (Commute.pow_pow_self b j l))

omit [Algebra ℝ R] in
theorem nilpotent_two_variable_monomial (a b : R) (hc : Commute a b)
    (ha : IsNilpotent a) (hb : IsNilpotent b) (i j : ℕ) (hij : 0 < i + j) :
    IsNilpotent (a ^ i * b ^ j) := by
  by_cases hi : 0 < i
  · exact (hc.pow_pow i j).isNilpotent_mul_right (IsNilpotent.pow_of_pos ha (Nat.ne_of_gt hi))
  · exact (hc.pow_pow i j).isNilpotent_mul_left (IsNilpotent.pow_of_pos hb (by omega))

theorem nilpotent_two_variable_polynomial {ι : Type*}
    (a b : R) (hc : Commute a b) (ha : IsNilpotent a) (hb : IsNilpotent b)
    (s : Finset ι) (c : ι → ℝ) (i j : ι → ℕ) (hij : ∀ t ∈ s, 0 < i t + j t) :
    IsNilpotent (∑ t ∈ s, c t • (a ^ i t * b ^ j t)) := by
  apply Commute.isNilpotent_sum
  · intro t ht
    exact (nilpotent_two_variable_monomial a b hc ha hb (i t) (j t) (hij t ht)).smul (c t)
  · intro t u _ _
    exact ((commute_two_variable_monomials a b hc (i t) (j t) (i u) (j u)).smul_left
      (c t)).smul_right (c u)

omit [Algebra ℝ R] in
theorem commuting_unipotent_product (a b : R) (hc : Commute a b)
    (ha : IsNilpotent (a - 1)) (hb : IsNilpotent (b - 1)) :
    IsNilpotent (a * b - 1) := by
  have hab : Commute (a - 1) (b - 1) :=
    (hc.sub_right (Commute.one_right a)).sub_left
      ((Commute.one_left b).sub_right (Commute.refl 1))
  have hm : IsNilpotent ((a - 1) * (b - 1)) := hab.isNilpotent_mul_right ha
  have hs : IsNilpotent ((a - 1) + (b - 1)) := hab.isNilpotent_add ha hb
  have hcomm : Commute ((a - 1) * (b - 1)) ((a - 1) + (b - 1)) :=
    ((Commute.refl (a - 1)).mul_left hab.symm).add_right
      (hab.mul_left (Commute.refl (b - 1)))
  convert hcomm.isNilpotent_add hm hs using 1
  noncomm_ring

end

/-! The polynomial giving an exponential derivative is unipotent when
its two commuting arguments are nilpotent. -/

variable {R : Type*} [Ring R] [Algebra ℝ R]

def exponentialDerivativePolynomial (m : ℕ) (a b : R) : R :=
  ∑ n ∈ Finset.range m, (n.factorial⁻¹ : ℝ) •
    ∑ i ∈ Finset.range n, a ^ (n.pred - i) * b ^ i

theorem exponentialDerivativePolynomial_sub_one (m : ℕ) (a b : R) :
    exponentialDerivativePolynomial (m + 2) a b - 1 =
      ∑ n ∈ Finset.range m, ((n + 2).factorial⁻¹ : ℝ) •
        ∑ i ∈ Finset.range (n + 2), a ^ (n + 1 - i) * b ^ i := by
  unfold exponentialDerivativePolynomial
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp

theorem exponentialDerivativePolynomial_unipotent (m : ℕ) (a b : R)
    (hc : Commute a b) (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent (exponentialDerivativePolynomial (m + 2) a b - 1) := by
  rw [exponentialDerivativePolynomial_sub_one]
  apply Commute.isNilpotent_sum
  · intro n _
    apply IsNilpotent.smul
    convert nilpotent_two_variable_polynomial a b hc ha hb (Finset.range (n + 2))
      (fun _ => 1) (fun i => n + 1 - i) (fun i => i) (fun i hi => ?_) using 1
    · simp only [one_smul]
    · have hi' := Finset.mem_range.mp hi
      omega
  · intro n k _ _
    apply Commute.smul_right
    apply Commute.smul_left
    apply Commute.sum_left
    intro i _
    apply Commute.sum_right
    intro j _
    exact commute_two_variable_monomials a b hc _ _ _ _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingNilpotentPolynomials.Construction
