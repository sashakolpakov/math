import OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomial
import Mathlib.Algebra.Polynomial.Roots

/-! # Eventual Polynomial -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.EventualPolynomial.Construction

noncomputable section

/-! Canonical polynomials of actual eventually polynomial numerical sequences. -/

open OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomial

theorem polynomial_eq_of_eventual_nat_eval (P Q : Polynomial ℚ) (b : ℕ)
    (h : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) = Q.eval (n : ℚ)) : P = Q := by
  have hi : Function.Injective (fun n : ℕ => ((n + b : ℕ) : ℚ)) := by
    intro m n hmn
    exact Nat.add_right_cancel (Nat.cast_injective hmn)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hi).mono
  rintro x ⟨n, rfl⟩
  exact h (n + b) (by omega)

def eventualPolynomialValue {f : ℕ → ℚ} (h : SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial f) : Polynomial ℚ := h.choose

theorem eventualPolynomialValue_spec {f : ℕ → ℚ} (h : SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial f) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → f n = (eventualPolynomialValue h).eval (n : ℚ) :=
  h.choose_spec

theorem eventualPolynomialValue_eq {f : ℕ → ℚ} (h : SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial f)
    (P : Polynomial ℚ) (b : ℕ) (hb : ∀ n : ℕ, b ≤ n → f n = P.eval (n : ℚ)) :
    eventualPolynomialValue h = P := by
  obtain ⟨c, hc⟩ := eventualPolynomialValue_spec h
  apply polynomial_eq_of_eventual_nat_eval _ _ (max b c)
  intro n hn
  exact (hc n ((le_max_right b c).trans hn)).symm.trans
    (hb n ((le_max_left b c).trans hn))

theorem eventualPolynomialValue_congr {f g : ℕ → ℚ}
    (hf : SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial f) (hg : SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial g)
    (b : ℕ) (hb : ∀ n : ℕ, b ≤ n → f n = g n) :
    eventualPolynomialValue hf = eventualPolynomialValue hg := by
  obtain ⟨c, hc⟩ := eventualPolynomialValue_spec hg
  apply eventualPolynomialValue_eq hf _ (max b c)
  intro n hn
  exact (hb n ((le_max_left b c).trans hn)).trans (hc n ((le_max_right b c).trans hn))

theorem eventualPolynomialValue_add {f g : ℕ → ℚ}
    (hf : SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial f) (hg : SheafCohomology.Projective.EventualPolynomial.EventuallyPolynomial g) :
    eventualPolynomialValue (hf.add hg) = eventualPolynomialValue hf + eventualPolynomialValue hg := by
  obtain ⟨b, hb⟩ := eventualPolynomialValue_spec hf
  obtain ⟨c, hc⟩ := eventualPolynomialValue_spec hg
  apply eventualPolynomialValue_eq _ _ (max b c)
  intro n hn
  rw [hb n ((le_max_left b c).trans hn), hc n ((le_max_right b c).trans hn), Polynomial.eval_add]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.EventualPolynomial.Construction
