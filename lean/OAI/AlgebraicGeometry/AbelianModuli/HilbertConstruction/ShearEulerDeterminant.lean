import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.IntegerMultiples
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShearEulerIdentity

/-! # Shear Euler Determinant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShearEulerDeterminant

/-! Separate polynomiality and integer shears determine the entire
quadratic determinant formula, including degenerate and negative classes. -/

theorem shear_euler_determinant_formula
    (F : ℤ → ℤ → ℤ → ℚ) (g : ℕ) (d : ℚ)
    (hpolyA : ∀ b c : ℤ, ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a b c)
    (hpolyC : ∀ a b : ℤ, ∃ P : Polynomial ℚ, ∀ c : ℤ, P.eval (c : ℚ) = F a b c)
    (hshear : ∀ a b c t : ℤ, F a b c = F a (b + t * c + t ^ 2 * a) (c + 2 * t * a))
    (hdiag : ∀ a b : ℤ, F a b 0 = d * (a : ℚ) ^ g * (b : ℚ) ^ g)
    (a b c : ℤ) :
    (4 : ℚ) ^ g * F a b c = d * (4 * (a : ℚ) * (b : ℚ) - (c : ℚ) ^ 2) ^ g := by
  have hnonzero (a b c : ℤ) (ha : a ≠ 0) :
      (4 : ℚ) ^ g * F a b c = d * (4 * (a : ℚ) * (b : ℚ) - (c : ℚ) ^ 2) ^ g := by
    obtain ⟨P, hP⟩ := hpolyC a b
    let Q : Polynomial ℚ := Polynomial.C d *
      (Polynomial.C (4 * (a : ℚ) * (b : ℚ)) - Polynomial.X ^ 2) ^ g
    have he : Polynomial.C ((4 : ℚ) ^ g) * P = Q := by
      apply HilbertConstruction.Polynomial.IntegerMultiples.polynomial_eq_of_positive_integer_multiple_evals _ _ (2 * a)
        (mul_ne_zero (by norm_num) ha)
      intro n _hn
      have hb : (b - a * (n : ℤ) ^ 2) + (n : ℤ) * 0 + (n : ℤ) ^ 2 * a = b := by ring
      have hc : (0 : ℤ) + 2 * (n : ℤ) * a = (2 * a) * (n : ℤ) := by ring
      have hs := hshear a (b - a * (n : ℤ) ^ 2) 0 (n : ℤ)
      rw [hb, hc] at hs
      have hv := hP ((2 * a) * (n : ℤ))
      rw [Int.cast_mul, Int.cast_natCast] at hv
      rw [Polynomial.eval_mul, Polynomial.eval_C, hv, ← hs, hdiag]
      change (4 : ℚ) ^ g * (d * (a : ℚ) ^ g * ((b - a * (n : ℤ) ^ 2 : ℤ) : ℚ) ^ g) =
        Q.eval (((2 * a : ℤ) : ℚ) * (n : ℚ))
      have heval : Q.eval (((2 * a : ℤ) : ℚ) * (n : ℚ)) =
          d * (4 * (a : ℚ) * (b : ℚ) - (2 * (a : ℚ) * (n : ℚ)) ^ 2) ^ g := by
        simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_X, Int.cast_mul, Int.cast_ofNat]
      rw [heval, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      calc
        _ = d * (4 * (a : ℚ) * ((b : ℚ) - (a : ℚ) * (n : ℚ) ^ 2)) ^ g := by
          rw [mul_pow, mul_pow]
          ring
        _ = _ := congrArg (fun z : ℚ => d * z ^ g) (by ring)
    have hv := congrArg (fun Q : Polynomial ℚ => Q.eval (c : ℚ)) he
    simpa only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, hP c] using hv
  obtain ⟨P, hP⟩ := hpolyA b c
  let Q : Polynomial ℚ := Polynomial.C d *
    (Polynomial.C (4 * (b : ℚ)) * Polynomial.X - Polynomial.C ((c : ℚ) ^ 2)) ^ g
  have he : Polynomial.C ((4 : ℚ) ^ g) * P = Q := by
    apply HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals
    intro n hn
    have hv := hP (n : ℤ)
    rw [Int.cast_natCast] at hv
    rw [Polynomial.eval_mul, Polynomial.eval_C, hv]
    have h := hnonzero (n : ℤ) b c (by exact_mod_cast (Nat.ne_of_gt hn))
    rw [Int.cast_natCast] at h
    change (4 : ℚ) ^ g * F (n : ℤ) b c = Q.eval (n : ℚ)
    rw [h]
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X]
    congr 2
    ring
  have hv := congrArg (fun Q : Polynomial ℚ => Q.eval (a : ℚ)) he
  simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, hP a] at hv
  exact hv.trans (congrArg (fun z : ℚ => d * z ^ g) (by ring))

theorem shear_euler_addition_value
    (F : ℤ → ℤ → ℤ → ℚ) (g : ℕ) (d : ℚ)
    (hpolyA : ∀ b c : ℤ, ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a b c)
    (hpolyC : ∀ a b : ℤ, ∃ P : Polynomial ℚ, ∀ c : ℤ, P.eval (c : ℚ) = F a b c)
    (hshear : ∀ a b c t : ℤ, F a b c = F a (b + t * c + t ^ 2 * a) (c + 2 * t * a))
    (hdiag : ∀ a b : ℤ, F a b 0 = d * (a : ℚ) ^ g * (b : ℚ) ^ g) :
    F 2 2 2 = d * (3 : ℚ) ^ g := by
  have h := shear_euler_determinant_formula F g d hpolyA hpolyC hshear hdiag 2 2 2
  norm_num at h
  apply mul_left_cancel₀ (pow_ne_zero g (show (4 : ℚ) ≠ 0 by norm_num))
  calc
    (4 : ℚ) ^ g * F 2 2 2 = d * (12 : ℚ) ^ g := h
    _ = (4 : ℚ) ^ g * (d * (3 : ℚ) ^ g) := by
      rw [show (12 : ℚ) = 4 * 3 by norm_num, mul_pow]
      ring

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShearEulerDeterminant
