import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EulerShifts

/-! # Integer Orbit Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerOrbitPolynomial

/-! If every translated group orbit is polynomial on nonnegative powers,
its polynomial already computes all integer powers, including inverse powers. -/

theorem polynomial_orbit_all_integers
    {G : Type*} [Group G] (f : G → ℚ) (a : G)
    (hpoly : ∀ q : G, ∃ P : Polynomial ℚ, ∀ n : ℕ, P.eval (n : ℚ) = f (q * a ^ n))
    (q : G) (P : Polynomial ℚ) (hP : ∀ n : ℕ, P.eval (n : ℚ) = f (q * a ^ n)) (z : ℤ) :
    P.eval (z : ℚ) = f (q * a ^ z) := by
  cases z with
  | ofNat n =>
      change P.eval ((n : ℤ) : ℚ) = f (q * a ^ (n : ℤ))
      rw [Int.cast_natCast, zpow_natCast]
      exact hP n
  | negSucc k =>
      let q' := q * (a ^ (k + 1))⁻¹
      obtain ⟨Q, hQ⟩ := hpoly q'
      have he : Q.comp (Polynomial.X + Polynomial.C ((k + 1 : ℕ) : ℚ)) = P := by
        apply HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals
        intro n _hn
        rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
          ← Nat.cast_add, hQ, hP]
        apply congrArg f
        change (q * (a ^ (k + 1))⁻¹) * a ^ (n + (k + 1)) = q * a ^ n
        rw [Nat.add_comm n (k + 1), pow_add a (k + 1) n, mul_assoc, inv_mul_cancel_left]
      have heval := congrArg (fun F : Polynomial ℚ => F.eval (-((k + 1 : ℕ) : ℚ))) he
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, neg_add_cancel] at heval
      have hz : P.eval (-((k + 1 : ℕ) : ℚ)) = f q' := heval.symm.trans (by
        simpa only [Nat.cast_zero, pow_zero, mul_one] using hQ 0)
      rw [Int.cast_negSucc, zpow_negSucc]
      exact hz

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerOrbitPolynomial
