import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.IntegerStep

/-! # Shear Euler Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShearEulerIdentity

/-! Integer shear symmetries determine the Euler coefficient of the
biextension direction from the external-product Euler monomial. -/

theorem shear_euler_coefficient_identity
    (F : ℤ → ℤ → ℤ → ℚ) (g : ℕ) (d : ℚ)
    (hpolyA : ∀ c : ℤ, ∃ P : Polynomial ℚ, ∀ a : ℤ, P.eval (a : ℚ) = F a 0 c)
    (hpolyC : ∃ P : Polynomial ℚ, ∀ c : ℤ, P.eval (c : ℚ) = F 0 0 c)
    (hswap : ∀ a b c : ℤ, F a b c = F b a c)
    (hshear : ∀ a b c t : ℤ, F a b c = F a (b + t * c + t ^ 2 * a) (c + 2 * t * a))
    (hdiag : ∀ a b : ℤ, F a b 0 = d * (a : ℚ) ^ g * (b : ℚ) ^ g) :
    (2 : ℚ) ^ (2 * g) * F 0 0 1 = (-1 : ℚ) ^ g * d := by
  have hzero (c : ℤ) (hc : c ≠ 0) : F 1 0 c = F 0 0 c := by
    obtain ⟨P, hP⟩ := hpolyA c
    have hstep (t : ℤ) : F 0 0 c = F (t * c) 0 c := by
      have h := hshear 0 0 c t
      simp only [mul_zero, zero_add, add_zero] at h
      exact h.trans (hswap 0 (t * c) c)
    have hconst : P.eval 1 = P.eval 0 :=
      HilbertConstruction.Polynomial.IntegerStep.polynomial_eval_one_of_constant_integer_multiples P c hc (by
        intro n _hn
        have hn := hP (c * (n : ℤ))
        have h0 := hP 0
        simp only [Int.cast_mul, Int.cast_natCast] at hn
        simp only [Int.cast_zero] at h0
        rw [hn, h0]
        simpa only [mul_comm] using (hstep (n : ℤ)).symm)
    have h1 := hP 1
    have h0 := hP 0
    simp only [Int.cast_one] at h1
    simp only [Int.cast_zero] at h0
    exact h1.symm.trans (hconst.trans h0)
  have hdouble (m : ℕ) (hm : 0 < m) :
      F 0 0 (2 * (m : ℤ)) = d * (-1 : ℚ) ^ g * (m : ℚ) ^ (2 * g) := by
    have hm' : 0 < (m : ℤ) := by exact_mod_cast hm
    have hc : 2 * (m : ℤ) ≠ 0 := by omega
    have hb : (0 : ℤ) + (-(m : ℤ)) * (2 * (m : ℤ)) + (-(m : ℤ)) ^ 2 * 1 = -((m : ℤ) ^ 2) := by ring
    have ht : 2 * (m : ℤ) + 2 * (-(m : ℤ)) * 1 = 0 := by ring
    have hs : F 1 0 (2 * (m : ℤ)) = F 1 (-((m : ℤ) ^ 2)) 0 := by
      simpa only [hb, ht] using hshear 1 0 (2 * (m : ℤ)) (-(m : ℤ))
    calc
      _ = F 1 0 (2 * (m : ℤ)) := (hzero _ hc).symm
      _ = F 1 (-((m : ℤ) ^ 2)) 0 := hs
      _ = d * (1 : ℚ) ^ g * ((-((m : ℤ) ^ 2) : ℤ) : ℚ) ^ g := by
        simpa only [Int.cast_one] using hdiag 1 (-((m : ℤ) ^ 2))
      _ = _ := by
        have hmcast : ((-((m : ℤ) ^ 2) : ℤ) : ℚ) = (-1 : ℚ) * (m : ℚ) ^ 2 := by
          rw [Int.cast_neg, Int.cast_pow, Int.cast_natCast, neg_one_mul]
        rw [one_pow, mul_one, hmcast, mul_pow, ← pow_mul, mul_assoc]
  obtain ⟨P, hP⟩ := hpolyC
  have he : P.comp (Polynomial.C (2 : ℚ) * Polynomial.X) =
      Polynomial.monomial (2 * g) (d * (-1 : ℚ) ^ g) := by
    apply HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals
    intro m hm
    have hv := hP (2 * (m : ℤ))
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at hv
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      hv, hdouble m hm, Polynomial.eval_monomial]
  have hv := congrArg (fun Q : Polynomial ℚ => Q.eval (2 : ℚ)⁻¹) he
  have ht : (2 : ℚ) ≠ 0 := by norm_num
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_monomial, mul_inv_cancel₀ ht] at hv
  have h1 : P.eval 1 = F 0 0 1 := by simpa only [Int.cast_one] using hP 1
  rw [h1] at hv
  have hpow : (2 : ℚ) ^ (2 * g) * ((2 : ℚ)⁻¹) ^ (2 * g) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]
  rw [hv]
  calc
    _ = ((2 : ℚ) ^ (2 * g) * ((2 : ℚ)⁻¹) ^ (2 * g)) * ((-1 : ℚ) ^ g * d) := by ring
    _ = _ := by rw [hpow, one_mul]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ShearEulerIdentity
