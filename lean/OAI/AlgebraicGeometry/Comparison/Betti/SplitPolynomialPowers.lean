import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span

/-! # Split Polynomial Powers -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SplitPolynomialPowers.AnalyticLocal

noncomputable section

section

/-! A split coefficient inclusion and a regular coordinate identify
divisibility by coordinate powers on polynomials exactly. -/

open _root_.Polynomial

variable {A B : Type*} [CommRing A] [CommRing B] [IsDomain B]

omit [IsDomain B] in
theorem retract_polynomial_eval (s : A →+* B) (r : B →+* A) (hrs : r.comp s = RingHom.id A)
    (t : B) (hrt : r t = 0) (P : A[X]) : r (P.eval₂ s t) = P.coeff 0 := by
  rw [hom_eval₂, hrs, hrt]
  change P.eval 0 = P.coeff 0
  rw [coeff_zero_eq_eval_zero]

theorem coordinate_pow_dvd_polynomial_eval (s : A →+* B) (r : B →+* A)
    (hrs : r.comp s = RingHom.id A) (t : B) (hrt : r t = 0) (ht : t ≠ 0)
    (n : ℕ) (P : A[X]) : t ^ n ∣ P.eval₂ s t ↔ X ^ n ∣ P := by
  constructor
  · induction n generalizing P with
    | zero => simp
    | succ n ih =>
      intro h
      obtain ⟨b, hb⟩ := h
      have hconstant : P.coeff 0 = 0 := by
        rw [← retract_polynomial_eval s r hrs t hrt P, hb, map_mul, map_pow, hrt,
          zero_pow (Nat.succ_ne_zero n), zero_mul]
      obtain ⟨Q, hPQ⟩ := X_dvd_iff.mpr hconstant
      have hQ : t ^ n ∣ Q.eval₂ s t := by
        refine ⟨b, ?_⟩
        apply mul_left_cancel₀ ht
        calc
          t * Q.eval₂ s t = P.eval₂ s t := by rw [hPQ, eval₂_mul, eval₂_X]
          _ = t * (t ^ n * b) := by rw [hb, pow_succ', mul_assoc]
      obtain ⟨S, hS⟩ := ih Q hQ
      exact ⟨S, by rw [hPQ, hS, pow_succ', mul_assoc]⟩
  · intro h
    have he := map_dvd (eval₂RingHom s t) h
    change (X ^ n).eval₂ s t ∣ P.eval₂ s t at he
    simpa only [eval₂_pow, eval₂_X] using he

end

/-! Polynomial and ambient quotients by every power of a split regular
coordinate agree via actual evaluation. -/

open _root_.Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

def truncatedPolynomialMap (s : A →+* B) (t : B) (n : ℕ) :
    A[X] ⧸ Ideal.span {(X : A[X]) ^ n} →+* B ⧸ Ideal.span {t ^ n} :=
  Ideal.quotientMap (Ideal.span {t ^ n}) (eval₂RingHom s t) (by
    apply Ideal.span_le.mpr
    rintro P (rfl : P = X ^ n)
    change (X ^ n).eval₂ s t ∈ Ideal.span {t ^ n}
    rw [eval₂_pow, eval₂_X]
    exact Ideal.mem_span_singleton_self _)

theorem truncatedPolynomialMap_mk (s : A →+* B) (t : B) (n : ℕ) (P : A[X]) :
    truncatedPolynomialMap s t n (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk (Ideal.span {t ^ n}) (P.eval₂ s t) := rfl

theorem split_polynomial_approximation (s : A →+* B) (r : B →+* A) (t : B)
    (hdivision : ∀ y : B, ∃ b : B, y = s (r y) + t * b) (n : ℕ) (y : B) :
    ∃ (P : A[X]) (b : B), y = P.eval₂ s t + t ^ n * b := by
  induction n generalizing y with
  | zero => exact ⟨0, y, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := hdivision y
    obtain ⟨P, b, hP⟩ := ih q
    refine ⟨C (r y) + X * P, b, ?_⟩
    rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    calc
      y = s (r y) + t * q := hq
      _ = s (r y) + t * P.eval₂ s t + t ^ (n + 1) * b := by
        rw [hP, mul_add, pow_succ', mul_assoc, add_assoc]

theorem truncatedPolynomialMap_surjective (s : A →+* B) (r : B →+* A) (t : B)
    (hdivision : ∀ y : B, ∃ b : B, y = s (r y) + t * b) (n : ℕ) :
    Function.Surjective (truncatedPolynomialMap s t n) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨P, b, hy⟩ := split_polynomial_approximation s r t hdivision n y
  refine ⟨Ideal.Quotient.mk _ P, ?_⟩
  rw [truncatedPolynomialMap_mk, hy, map_add, map_mul]
  have hz : Ideal.Quotient.mk (Ideal.span {t ^ n}) (t ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [hz, zero_mul, add_zero]

theorem truncatedPolynomialMap_injective [IsDomain B] (s : A →+* B) (r : B →+* A)
    (hrs : r.comp s = RingHom.id A) (t : B) (hrt : r t = 0) (ht : t ≠ 0) (n : ℕ) :
    Function.Injective (truncatedPolynomialMap s t n) := by
  apply Ideal.quotientMap_injective'
  intro P hP
  change P.eval₂ s t ∈ Ideal.span {t ^ n} at hP
  rw [Ideal.mem_span_singleton] at hP ⊢
  exact (coordinate_pow_dvd_polynomial_eval s r hrs t hrt ht n P).mp hP

def splitPolynomialQuotientEquiv [IsDomain B] (s : A →+* B) (r : B →+* A)
    (hrs : r.comp s = RingHom.id A) (t : B) (hrt : r t = 0) (ht : t ≠ 0)
    (hdivision : ∀ y : B, ∃ b : B, y = s (r y) + t * b) (n : ℕ) :
    A[X] ⧸ Ideal.span {(X : A[X]) ^ n} ≃+* B ⧸ Ideal.span {t ^ n} :=
  RingEquiv.ofBijective (truncatedPolynomialMap s t n)
    ⟨truncatedPolynomialMap_injective s r hrs t hrt ht n,
      truncatedPolynomialMap_surjective s r t hdivision n⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.SplitPolynomialPowers.AnalyticLocal
