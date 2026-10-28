import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentExponents
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Laurent Monomials -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech

noncomputable section

/-! Laurent monomials in the actual principal localizations of polynomial rings. -/

open _root_.MvPolynomial

universe u v

variable {σ : Type u} [Fintype σ] [DecidableEq σ]
variable (R : Type v) [CommRing R]

def inversionMonomial (s : Finset σ) : MvPolynomial σ R := monomial (LaurentExponents.ProjectiveCech.inversionExponent s) 1

omit [Fintype σ] [DecidableEq σ] in
theorem inversionMonomial_regular (s : Finset σ) : IsRegular (inversionMonomial R s) :=
  isRegular_one.monomial

omit [Fintype σ] [DecidableEq σ] in
theorem inversionMonomial_pow (s : Finset σ) (k : ℕ) :
    inversionMonomial R s ^ k = monomial (k • LaurentExponents.ProjectiveCech.inversionExponent s) 1 := by
  rw [inversionMonomial, monomial_pow, one_pow]

abbrev ChartLocalization (s : Finset σ) := Localization.Away (inversionMonomial R s)

omit [Fintype σ] [DecidableEq σ] in
theorem chartLocalization_injective (s : Finset σ) :
    Function.Injective (algebraMap (MvPolynomial σ R) (ChartLocalization R s)) := by
  apply IsLocalization.injective (M := Submonoid.powers (inversionMonomial R s))
  rintro x ⟨k, rfl⟩
  exact isRegular_iff_mem_nonZeroDivisors.mp ((inversionMonomial_regular R s).pow k)

def chartDenominator (s : Finset σ) (k : ℕ) : Submonoid.powers (inversionMonomial R s) :=
  ⟨inversionMonomial R s ^ k, ⟨k, rfl⟩⟩

def fractionAt {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s) (k : ℕ) : ChartLocalization R s :=
  IsLocalization.mk' (ChartLocalization R s) (monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) 1)
    (chartDenominator R s k)

omit [DecidableEq σ] in
theorem fractionAt_eq_of_nonnegative {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s) (k l : ℕ)
    (hk : ∀ i, 0 ≤ a.val i + (k : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent s i : ℤ))
    (hl : ∀ i, 0 ≤ a.val i + (l : ℤ) * (LaurentExponents.ProjectiveCech.inversionExponent s i : ℤ)) :
    fractionAt R a k = fractionAt R a l := by
  apply IsLocalization.mk'_eq_of_eq
  change inversionMonomial R s ^ k * monomial (LaurentExponents.ProjectiveCech.numeratorExponent a l) 1 =
    inversionMonomial R s ^ l * monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) 1
  rw [inversionMonomial_pow, inversionMonomial_pow, monomial_mul_monomial, monomial_mul_monomial, one_mul]
  apply congrArg (fun d => monomial d (1 : R))
  simpa only [add_comm] using (LaurentExponents.ProjectiveCech.numeratorExponent_balance_of_nonnegative a k l hk hl).symm

theorem fractionAt_eq {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s) (k l : ℕ)
    (hk : LaurentExponents.ProjectiveCech.denominatorBound a ≤ k) (hl : LaurentExponents.ProjectiveCech.denominatorBound a ≤ l) :
    fractionAt R a k = fractionAt R a l := by
  apply IsLocalization.mk'_eq_of_eq
  change inversionMonomial R s ^ k * monomial (LaurentExponents.ProjectiveCech.numeratorExponent a l) 1 =
    inversionMonomial R s ^ l * monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) 1
  rw [inversionMonomial_pow, inversionMonomial_pow, monomial_mul_monomial, monomial_mul_monomial, one_mul]
  apply congrArg (fun d => monomial d (1 : R))
  simpa only [add_comm] using (LaurentExponents.ProjectiveCech.numeratorExponent_balance a k l hk hl).symm

def laurentMonomial {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s) : ChartLocalization R s :=
  fractionAt R a (LaurentExponents.ProjectiveCech.denominatorBound a)

theorem laurentMonomial_fractionAt {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s) (k : ℕ)
    (hk : LaurentExponents.ProjectiveCech.denominatorBound a ≤ k) : laurentMonomial R a = fractionAt R a k :=
  fractionAt_eq R a _ _ le_rfl hk

theorem laurentMonomial_clear {s : Finset σ} (a : LaurentExponents.ProjectiveCech.LaurentExponent s) (k : ℕ)
    (hk : LaurentExponents.ProjectiveCech.denominatorBound a ≤ k) :
    algebraMap (MvPolynomial σ R) (ChartLocalization R s) (inversionMonomial R s ^ k) * laurentMonomial R a =
      algebraMap (MvPolynomial σ R) (ChartLocalization R s) (monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) 1) := by
  rw [laurentMonomial_fractionAt R a k hk]
  exact IsLocalization.mk'_spec' (ChartLocalization R s)
    (monomial (LaurentExponents.ProjectiveCech.numeratorExponent a k) 1) (chartDenominator R s k)

theorem laurentMonomial_ofNumerator (s : Finset σ) (d : σ →₀ ℕ) (k : ℕ) :
    laurentMonomial R (LaurentExponents.ProjectiveCech.exponentOfNumerator s d k) =
      IsLocalization.mk' (ChartLocalization R s) (monomial d 1)
        (chartDenominator R s k) := by
  rw [laurentMonomial, fractionAt_eq_of_nonnegative R (LaurentExponents.ProjectiveCech.exponentOfNumerator s d k) _ k
    (LaurentExponents.ProjectiveCech.clearedExponent_nonnegative _ _ le_rfl) (LaurentExponents.ProjectiveCech.exponentOfNumerator_clear s d k)]
  simp only [fractionAt, LaurentExponents.ProjectiveCech.numeratorExponent_exponentOfNumerator]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentMonomials.ProjectiveCech
