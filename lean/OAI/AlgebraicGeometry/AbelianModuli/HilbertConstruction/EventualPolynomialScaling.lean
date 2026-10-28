import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.DilationMonomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-! # Eventual Polynomial Scaling -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EventualPolynomialScaling

noncomputable section

/-! An eventually polynomial sequence with an expanding power-weight scaling law has the exact monomial polynomial, with coefficient determined by its value at one. -/

theorem eventualPolynomial_dilation (f : ℕ → ℚ) (P : Polynomial ℚ) (a g : ℕ)
    (ha : 0 < a) (hscale : ∀ n, f (n * a) = (a : ℚ) ^ g * f n)
    (hP : ∃ b : ℕ, ∀ n, b ≤ n → P.eval (n : ℚ) = f n) :
    P.comp (Polynomial.C (a : ℚ) * Polynomial.X) = Polynomial.C ((a : ℚ) ^ g) * P := by
  obtain ⟨b, hb⟩ := hP
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun m : ℕ => ((b + m : ℕ) : ℚ)) := by
    intro m n h
    exact Nat.add_left_cancel (Nat.cast_injective h)
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro x ⟨m, rfl⟩
  have hbm : b ≤ b + m := Nat.le_add_right _ _
  have hbma : b ≤ (b + m) * a := hbm.trans (Nat.le_mul_of_pos_right _ ha)
  calc
    (P.comp (Polynomial.C (a : ℚ) * Polynomial.X)).eval ((b + m : ℕ) : ℚ) =
        P.eval (((b + m) * a : ℕ) : ℚ) := by
      simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Nat.cast_mul, mul_comm (a : ℚ) ((b + m : ℕ) : ℚ)]
    _ = f ((b + m) * a) := hb _ hbma
    _ = (a : ℚ) ^ g * f (b + m) := hscale _
    _ = (Polynomial.C ((a : ℚ) ^ g) * P).eval ((b + m : ℕ) : ℚ) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, hb _ hbm]

theorem eventualPolynomial_scaling_monomial (f : ℕ → ℚ) (P : Polynomial ℚ) (a g : ℕ)
    (ha : 1 < a) (hscale : ∀ n, f (n * a) = (a : ℚ) ^ g * f n)
    (hP : ∃ b : ℕ, ∀ n, b ≤ n → P.eval (n : ℚ) = f n) :
    P = Polynomial.monomial g (P.coeff g) := by
  have hqa : (1 : ℚ) < (a : ℚ) := Nat.cast_lt.mpr ha
  exact HilbertConstruction.Polynomial.DilationMonomial.polynomial_eq_monomial_of_dilation P (a : ℚ) g
    (pow_right_strictMono₀ hqa).injective
    (eventualPolynomial_dilation f P a g (Nat.zero_lt_one.trans ha) hscale hP)

theorem nat_index_le_dilation_pow (a : ℕ) (ha : 1 < a) (k : ℕ) : k ≤ a ^ k := by
  have ha0 : 0 < a := Nat.zero_lt_one.trans ha
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      calc
        k + 1 ≤ a ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ a ^ k + a ^ k :=
          Nat.add_le_add_left (Nat.succ_le_iff.mpr (pow_pos ha0 k)) _
        _ = a ^ k * 2 := (Nat.mul_two _).symm
        _ ≤ a ^ k * a := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt ha)
        _ = a ^ (k + 1) := (pow_succ a k).symm

theorem scalingSequence_iterate (f : ℕ → ℚ) (a g : ℕ)
    (hscale : ∀ n, f (n * a) = (a : ℚ) ^ g * f n) (m k : ℕ) :
    f (m * a ^ k) = ((a : ℚ) ^ g) ^ k * f m := by
  induction k with
  | zero => simp only [pow_zero, mul_one, one_mul]
  | succ k ih =>
      rw [pow_succ, ← Nat.mul_assoc, hscale, ih, pow_succ,
        ← mul_assoc, mul_comm ((a : ℚ) ^ g)]

theorem eventualPolynomial_scaling_value_one (f : ℕ → ℚ) (P : Polynomial ℚ) (a g : ℕ)
    (ha : 1 < a) (hscale : ∀ n, f (n * a) = (a : ℚ) ^ g * f n)
    (hP : ∃ b : ℕ, ∀ n, b ≤ n → P.eval (n : ℚ) = f n) :
    P = Polynomial.monomial g (f 1) := by
  have hmono := eventualPolynomial_scaling_monomial f P a g ha hscale hP
  have ha0 : 0 < a := Nat.zero_lt_one.trans ha
  have grow := nat_index_le_dilation_pow a ha
  have hs (k : ℕ) : f (a ^ k) = ((a : ℚ) ^ g) ^ k * f 1 := by
    simpa only [one_mul] using scalingSequence_iterate f a g hscale 1 k
  obtain ⟨b, hb⟩ := hP
  have he := hb (a ^ b) (grow b)
  rw [hmono, Polynomial.eval_monomial, Nat.cast_pow, hs] at he
  have hexp : ((a : ℚ) ^ b) ^ g = ((a : ℚ) ^ g) ^ b := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm b g]
  rw [hexp, mul_comm (P.coeff g)] at he
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha0)
  have hc : P.coeff g = f 1 :=
    mul_left_cancel₀ (pow_ne_zero b (pow_ne_zero g haq)) he
  exact hmono.trans (congrArg (fun c : ℚ => Polynomial.monomial g c) hc)

theorem eventualPolynomial_scaling_positive_values (f : ℕ → ℚ) (P : Polynomial ℚ) (a g : ℕ)
    (ha : 1 < a) (hscale : ∀ n, f (n * a) = (a : ℚ) ^ g * f n)
    (hP : ∃ b : ℕ, ∀ n, b ≤ n → P.eval (n : ℚ) = f n)
    (m : ℕ) (hm : 0 < m) : f m = f 1 * (m : ℚ) ^ g := by
  have hmono := eventualPolynomial_scaling_value_one f P a g ha hscale hP
  obtain ⟨b, hb⟩ := hP
  have hbound : b ≤ m * a ^ b := by
    calc
      b ≤ a ^ b := nat_index_le_dilation_pow a ha b
      _ = 1 * a ^ b := (one_mul _).symm
      _ ≤ m * a ^ b := Nat.mul_le_mul_right _ hm
  have he := hb (m * a ^ b) hbound
  rw [hmono, Polynomial.eval_monomial, Nat.cast_mul, Nat.cast_pow, mul_pow,
    scalingSequence_iterate f a g hscale m b] at he
  have hexp : ((a : ℚ) ^ b) ^ g = ((a : ℚ) ^ g) ^ b := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm b g]
  rw [hexp] at he
  have he' : ((a : ℚ) ^ g) ^ b * (f 1 * (m : ℚ) ^ g) =
      ((a : ℚ) ^ g) ^ b * f m := by
    calc
      _ = f 1 * ((m : ℚ) ^ g * ((a : ℚ) ^ g) ^ b) := by ac_rfl
      _ = _ := he
  have haq : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.zero_lt_one.trans ha))
  exact (mul_left_cancel₀ (pow_ne_zero b (pow_ne_zero g haq)) he').symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EventualPolynomialScaling
