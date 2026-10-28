import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Fully finite exponential-moment sampling. No measure space or randomized
algorithm is involved: all averages below are sums over finite function spaces. -/

namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators

variable {X A : Type*} [Fintype X] [Fintype A]

theorem sum_exp_le (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hzero : ∑ x, f x = 0) (t : ℝ) :
    (∑ x, Real.exp (t * f x)) ≤
      (Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2) := by
  calc
    (∑ x, Real.exp (t * f x)) ≤
        ∑ x, (Real.cosh t + f x * Real.sinh t) := by
      apply Finset.sum_le_sum
      intro x _
      simpa [mul_comm] using Real.exp_mul_le_cosh_add_mul_sinh (hf x) t
    _ = (Fintype.card X : ℝ) * Real.cosh t := by
      simp [Finset.sum_add_distrib, ← Finset.sum_mul, hzero]
    _ ≤ (Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq t) (by positivity)

theorem sum_exp_samples_le (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hzero : ∑ x, f x = 0) (D : ℕ) (t : ℝ) :
    (∑ s : Fin D → X, Real.exp (t * ∑ i, f (s i))) ≤
      (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * t ^ 2 / 2) := by
  classical
  have heq : (∑ s : Fin D → X, Real.exp (t * ∑ i, f (s i))) =
      (∑ x, Real.exp (t * f x)) ^ D := by
    simp_rw [Finset.mul_sum, Real.exp_sum]
    rw [← Fintype.prod_sum (fun (_ : Fin D) (x : X) => Real.exp (t * f x))]
    simp
  rw [heq]
  calc
    (∑ x, Real.exp (t * f x)) ^ D ≤
        ((Fintype.card X : ℝ) * Real.exp (t ^ 2 / 2)) ^ D := by
      exact pow_le_pow_left₀ (by positivity) (sum_exp_le f hf hzero t) D
    _ = (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * t ^ 2 / 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring

noncomputable def potential (f : A → X → ℝ) (D : ℕ) (ε : ℝ) (s : Fin D → X) : ℝ :=
  ∑ a, (Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)))

theorem sum_potential_le (f : A → X → ℝ) (hf : ∀ a x, |f a x| ≤ 1)
    (hzero : ∀ a, ∑ x, f a x = 0) (D : ℕ) (ε : ℝ) :
    (∑ s : Fin D → X, potential f D ε s) ≤
      (Fintype.card X : ℝ) ^ D *
        (2 * Fintype.card A * Real.exp ((D : ℝ) * ε ^ 2 / 2)) := by
  classical
  unfold potential
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ s : Fin D → X,
        (Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)))) ≤
        ∑ _a : A, (2 * (Fintype.card X : ℝ) ^ D *
          Real.exp ((D : ℝ) * ε ^ 2 / 2)) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Finset.sum_add_distrib]
      have hp := sum_exp_samples_le (f a) (hf a) (hzero a) D ε
      have hn := sum_exp_samples_le (f a) (hf a) (hzero a) D (-ε)
      simp only [neg_sq] at hn
      linarith
    _ = _ := by simp; ring

theorem exists_samples [Nonempty X] (f : A → X → ℝ)
    (hf : ∀ a x, |f a x| ≤ 1) (hzero : ∀ a, ∑ x, f a x = 0)
    (D : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbudget : 2 * (Fintype.card A : ℝ) < Real.exp ((D : ℝ) * ε ^ 2 / 2)) :
    ∃ s : Fin D → X, ∀ a, |∑ i, f a (s i)| ≤ ε * D := by
  classical
  by_contra h
  push Not at h
  have hpoint (s : Fin D → X) :
      Real.exp ((D : ℝ) * ε ^ 2) ≤ potential f D ε s := by
    obtain ⟨a, ha⟩ := h s
    have hterm : Real.exp ((D : ℝ) * ε ^ 2) ≤
        Real.exp (ε * ∑ i, f a (s i)) + Real.exp (-ε * ∑ i, f a (s i)) := by
      rcases le_total 0 (∑ i, f a (s i)) with hp | hn
      · rw [abs_of_nonneg hp] at ha
        have he := mul_le_mul_of_nonneg_left (le_of_lt ha) hε
        have : Real.exp ((D : ℝ) * ε ^ 2) ≤
            Real.exp (ε * ∑ i, f a (s i)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        linarith [Real.exp_pos (-ε * ∑ i, f a (s i))]
      · rw [abs_of_nonpos hn] at ha
        have he := mul_le_mul_of_nonneg_left (le_of_lt ha) hε
        have : Real.exp ((D : ℝ) * ε ^ 2) ≤
            Real.exp (-ε * ∑ i, f a (s i)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        linarith [Real.exp_pos (ε * ∑ i, f a (s i))]
    apply hterm.trans
    unfold potential
    exact Finset.single_le_sum
      (f := fun b : A => Real.exp (ε * ∑ i, f b (s i)) +
        Real.exp (-ε * ∑ i, f b (s i)))
      (fun b _ => by positivity) (Finset.mem_univ a)
  have hlo := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin D → X))) => hpoint s)
  have hhi := sum_potential_le f hf hzero D ε
  have hcard : (Fintype.card X : ℝ) ^ D > 0 := by
    exact pow_pos (by exact_mod_cast Fintype.card_pos) D
  have hstrict : (Fintype.card X : ℝ) ^ D *
      (2 * Fintype.card A * Real.exp ((D : ℝ) * ε ^ 2 / 2)) <
      (Fintype.card X : ℝ) ^ D * Real.exp ((D : ℝ) * ε ^ 2) := by
    apply mul_lt_mul_of_pos_left _ hcard
    have hh := mul_lt_mul_of_pos_right hbudget (Real.exp_pos ((D : ℝ) * ε ^ 2 / 2))
    rw [← Real.exp_add] at hh
    convert hh using 1 ; congr 1 ; ring
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow] at hlo
  linarith

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
