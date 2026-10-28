import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Laurent Exponents -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentExponents.ProjectiveCech

noncomputable section

/-!
Exponent bookkeeping for principal polynomial localizations. Negative
exponents are allowed precisely in the inverted variables, and a common
power of their product clears every denominator.
-/

universe u

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

def inversionExponent (s : Finset σ) : σ →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1

omit [Fintype σ] in
theorem inversionExponent_apply (s : Finset σ) (i : σ) :
    inversionExponent s i = if i ∈ s then 1 else 0 := by
  classical
  simp [inversionExponent, Finsupp.single_apply]

abbrev LaurentExponent (s : Finset σ) := {a : σ → ℤ // ∀ i ∉ s, 0 ≤ a i}

def denominatorBound {s : Finset σ} (a : LaurentExponent s) : ℕ := ∑ i, (-a.val i).toNat

omit [DecidableEq σ] in
theorem neg_exponent_le_bound {s : Finset σ} (a : LaurentExponent s) (i : σ) :
    -a.val i ≤ (denominatorBound a : ℤ) := by
  have h : (-a.val i).toNat ≤ denominatorBound a := by
    change (-a.val i).toNat ≤ ∑ j, (-a.val j).toNat
    exact Finset.single_le_sum (f := fun j : σ => (-a.val j).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h' : ((-a.val i).toNat : ℤ) ≤ (denominatorBound a : ℤ) := by exact_mod_cast h
  omega

theorem clearedExponent_nonnegative {s : Finset σ} (a : LaurentExponent s)
    (k : ℕ) (hk : denominatorBound a ≤ k) (i : σ) :
    0 ≤ a.val i + (k : ℤ) * (inversionExponent s i : ℤ) := by
  rw [inversionExponent_apply]
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi, Nat.cast_one, mul_one]
    have h := neg_exponent_le_bound a i
    have hk' : (denominatorBound a : ℤ) ≤ k := by exact_mod_cast hk
    omega
  · simpa only [ite_eq_right hi, Nat.cast_zero, mul_zero, add_zero] using a.property i hi

def numeratorExponent {s : Finset σ} (a : LaurentExponent s) (k : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a.val i + (k : ℤ) * (inversionExponent s i : ℤ)).toNat)

omit [DecidableEq σ] in
theorem numeratorExponent_cast_of_nonnegative {s : Finset σ} (a : LaurentExponent s) (k : ℕ)
    (hk : ∀ i, 0 ≤ a.val i + (k : ℤ) * (inversionExponent s i : ℤ)) (i : σ) :
    (numeratorExponent a k i : ℤ) = a.val i + (k : ℤ) * (inversionExponent s i : ℤ) :=
  Int.toNat_of_nonneg (hk i)

theorem numeratorExponent_cast {s : Finset σ} (a : LaurentExponent s) (k : ℕ)
    (hk : denominatorBound a ≤ k) (i : σ) :
    (numeratorExponent a k i : ℤ) = a.val i + (k : ℤ) * (inversionExponent s i : ℤ) :=
  Int.toNat_of_nonneg (clearedExponent_nonnegative a k hk i)

omit [DecidableEq σ] in
theorem numeratorExponent_balance_of_nonnegative {s : Finset σ} (a : LaurentExponent s)
    (k l : ℕ)
    (hk : ∀ i, 0 ≤ a.val i + (k : ℤ) * (inversionExponent s i : ℤ))
    (hl : ∀ i, 0 ≤ a.val i + (l : ℤ) * (inversionExponent s i : ℤ)) :
    numeratorExponent a k + l • inversionExponent s = numeratorExponent a l + k • inversionExponent s := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have h : (numeratorExponent a k i : ℤ) + (l : ℤ) * (inversionExponent s i : ℤ) =
      (numeratorExponent a l i : ℤ) + (k : ℤ) * (inversionExponent s i : ℤ) := by
    rw [numeratorExponent_cast_of_nonnegative a k hk, numeratorExponent_cast_of_nonnegative a l hl]
    ring
  exact_mod_cast h

theorem numeratorExponent_balance {s : Finset σ} (a : LaurentExponent s)
    (k l : ℕ) (hk : denominatorBound a ≤ k) (hl : denominatorBound a ≤ l) :
    numeratorExponent a k + l • inversionExponent s = numeratorExponent a l + k • inversionExponent s := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have h : (numeratorExponent a k i : ℤ) + (l : ℤ) * (inversionExponent s i : ℤ) =
      (numeratorExponent a l i : ℤ) + (k : ℤ) * (inversionExponent s i : ℤ) := by
    rw [numeratorExponent_cast a k hk, numeratorExponent_cast a l hl]
    ring
  exact_mod_cast h

theorem numeratorExponent_injective {s : Finset σ} (a b : LaurentExponent s)
    (k : ℕ) (ha : denominatorBound a ≤ k) (hb : denominatorBound b ≤ k)
    (h : numeratorExponent a k = numeratorExponent b k) : a = b := by
  apply Subtype.ext
  funext i
  have hi := congrArg (fun f : σ →₀ ℕ => (f i : ℤ)) h
  rw [numeratorExponent_cast a k ha, numeratorExponent_cast b k hb] at hi
  exact add_right_cancel hi

def exponentOfNumerator (s : Finset σ) (d : σ →₀ ℕ) (k : ℕ) : LaurentExponent s :=
  ⟨fun i => (d i : ℤ) - (k : ℤ) * (inversionExponent s i : ℤ), by
    intro i hi
    change 0 ≤ (d i : ℤ) - (k : ℤ) * (inversionExponent s i : ℤ)
    rw [inversionExponent_apply, ite_eq_right hi, Nat.cast_zero, mul_zero, sub_zero]
    exact Int.natCast_nonneg _⟩

omit [Fintype σ] in
theorem exponentOfNumerator_clear (s : Finset σ) (d : σ →₀ ℕ) (k : ℕ) (i : σ) :
    0 ≤ (exponentOfNumerator s d k).val i + (k : ℤ) * (inversionExponent s i : ℤ) := by
  change 0 ≤ (d i : ℤ) - (k : ℤ) * (inversionExponent s i : ℤ) +
    (k : ℤ) * (inversionExponent s i : ℤ)
  rw [sub_add_cancel]
  exact Int.natCast_nonneg _

theorem numeratorExponent_exponentOfNumerator (s : Finset σ) (d : σ →₀ ℕ) (k : ℕ) :
    numeratorExponent (exponentOfNumerator s d k) k = d := by
  ext i
  change Int.toNat ((d i : ℤ) - (k : ℤ) * (inversionExponent s i : ℤ) +
    (k : ℤ) * (inversionExponent s i : ℤ)) = d i
  rw [sub_add_cancel, Int.toNat_natCast]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LaurentExponents.ProjectiveCech
