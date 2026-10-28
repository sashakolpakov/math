import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPolynomial

namespace OAI.Algorithms

/-! The three-residue idempotent coefficient family.  The only coefficient
assumption is a supplied inverse `u` of two. -/

namespace SubexponentialSAT.SqrtLog.Idempotent

open Polynomial

variable {A O K : Type*} [CommRing A] [CommRing O] [CommRing K]

noncomputable def ternaryH : A[X] := X * (X - C 1) * (X - C 2)

noncomputable def initialPolynomial (u : A) : A[X] := C u * (X - C 1) * (X - C 2)

def initialValue (u x : A) : A := u * (x - 1) * (x - 2)

theorem ternaryH_monic : (ternaryH : A[X]).Monic :=
  (monic_X.mul (monic_X_sub_C 1)).mul (monic_X_sub_C 2)

theorem ternaryH_natDegree [Nontrivial A] : (ternaryH : A[X]).natDegree = 3 := by
  rw [ternaryH, ((monic_X.mul (monic_X_sub_C 1)).natDegree_mul (monic_X_sub_C 2)),
    monic_X.natDegree_mul (monic_X_sub_C 1)]
  rw [natDegree_X, natDegree_X_sub_C, natDegree_X_sub_C]

theorem ternaryH_ne_one [Nontrivial A] : (ternaryH : A[X]) ≠ 1 := by
  intro h
  have := congrArg Polynomial.natDegree h
  simp [ternaryH_natDegree] at this

theorem map_two (φ : A →+* O) : φ (2 : A) = (2 : O) := by
  rw [show (2 : A) = 1 + 1 by ring, map_add, map_one]
  ring

theorem map_initialValue (φ : A →+* O) (u x : A) :
    φ (initialValue u x) = initialValue (φ u) (φ x) := by
  simp only [initialValue, map_mul, map_sub, map_one, map_two]

theorem eval_initialPolynomial (φ : A →+* O) (u : A) (x : O) :
    (initialPolynomial u).eval₂ φ x = initialValue (φ u) x := by
  simp only [initialPolynomial, initialValue, eval₂_mul, eval₂_C, eval₂_sub,
    eval₂_X, eval₂_one, eval₂_ofNat, map_one, map_two]

theorem eval_ternaryH (φ : A →+* O) (x : O) :
    (ternaryH : A[X]).eval₂ φ x = x * (x - 1) * (x - 2) := by
  simp only [ternaryH, eval₂_mul, eval₂_sub, eval₂_X,
    eval₂_one, eval₂_ofNat, map_one, map_two]

theorem initialValue_error (u x : A) (hu : 2 * u = 1) :
    (initialValue u x) ^ 2 - initialValue u x =
      (x * (x - 1) * (x - 2)) * (u ^ 2 * (x - 3)) := by
  unfold initialValue
  linear_combination u * (x - 1) * (x - 2) * hu

theorem initialValue_zero (u : A) (hu : 2 * u = 1) : initialValue u 0 = 1 := by
  unfold initialValue
  linear_combination hu

@[simp] theorem initialValue_one (u : A) : initialValue u 1 = 0 := by
  simp [initialValue]

@[simp] theorem initialValue_two (u : A) : initialValue u 2 = 0 := by
  simp [initialValue]

noncomputable def liftedPolynomial (u : A) (t : ℕ) : A[X] :=
  normalized ((ternaryH : A[X]) ^ t) (initialPolynomial u) (Nat.clog 2 t)

noncomputable def coefficients (u : A) (t : ℕ) (s : Fin t) : A[X] :=
  digit ternaryH (liftedPolynomial u t) s

theorem coefficients_degree [Nontrivial A] (u : A) (t : ℕ) (s : Fin t) :
    (coefficients u t s).natDegree < 3 := by
  simpa only [coefficients, ternaryH_natDegree] using
    digit_natDegree_lt ternaryH (liftedPolynomial u t) ternaryH_monic ternaryH_ne_one s

theorem liftedPolynomial_degree [Nontrivial A] (u : A) (t : ℕ) :
    (liftedPolynomial u t).degree < ((ternaryH : A[X]) ^ t).degree :=
  normalized_degree _ _ (ternaryH_monic.pow t) _

theorem ternary_coordinate_length [Nontrivial A] (t : ℕ) :
    ((ternaryH : A[X]) ^ t).natDegree = 3 * t := by
  rw [ternaryH_monic.natDegree_pow, ternaryH_natDegree, Nat.mul_comm]

theorem lifted_eval_idempotent (φ : A →+* O) (u : A) (hu : 2 * u = 1)
    (t : ℕ) (x : O) (hx : ((ternaryH : A[X]).eval₂ φ x) ^ t = 0) :
    ((liftedPolynomial u t).eval₂ φ x) ^ 2 = (liftedPolynomial u t).eval₂ φ x := by
  have huO : (2 : O) * φ u = 1 := by
    have h := congrArg φ hu
    simpa only [map_mul, map_two, map_one] using h
  have hd : (ternaryH : A[X]).eval₂ φ x ∣
      ((initialPolynomial u).eval₂ φ x) ^ 2 - (initialPolynomial u).eval₂ φ x := by
    rw [eval_initialPolynomial, initialValue_error _ _ huO, eval_ternaryH]
    exact dvd_mul_right _ _
  unfold liftedPolynomial
  rw [eval_normalized _ _ (ternaryH_monic.pow t) φ x (by simpa only [eval₂_pow] using hx)]
  exact iterate_idempotent hd hx (Nat.le_pow_clog (by decide) t)

theorem coefficient_eval_sum (φ : A →+* O) (u : A) (t : ℕ) (x : O)
    (hx : ((ternaryH : A[X]).eval₂ φ x) ^ t = 0) :
    (liftedPolynomial u t).eval₂ φ x =
      ∑ s : Fin t, (coefficients u t s).eval₂ φ x * ((ternaryH : A[X]).eval₂ φ x) ^ (s : ℕ) := by
  rw [eval_expansion ternaryH (liftedPolynomial u t) t φ x hx]
  symm
  exact Fin.sum_univ_eq_sum_range (fun s =>
    (digit ternaryH (liftedPolynomial u t) s).eval₂ φ x *
      ((ternaryH : A[X]).eval₂ φ x) ^ s) t

theorem mapped_inverse_two (φ : A →+* O) {u : A} (hu : 2 * u = 1) :
    2 * φ u = 1 := by
  simpa only [map_mul, map_two, map_one] using congrArg φ hu

theorem eval_H_nilpotent (φ : A →+* O) (ρ : O →+* K) (q : O) (t : ℕ)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (x : O) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    ((ternaryH : A[X]).eval₂ φ x) ^ t = 0 := by
  have hres : ρ ((ternaryH : A[X]).eval₂ φ x) = 0 := by
    rw [eval_ternaryH]
    simp only [map_mul, map_sub, map_one, map_two]
    rcases hx with h | h | h <;> rw [h] <;> ring
  obtain ⟨c, hc⟩ := hker _ hres
  rw [hc, mul_pow, hq, zero_mul]

theorem lifted_eval_residue (φ : A →+* O) (ρ : O →+* K)
    (u : A) (t : ℕ) (x : O)
    (hx : ((ternaryH : A[X]).eval₂ φ x) ^ t = 0)
    (hi : (ρ ((initialPolynomial u).eval₂ φ x)) ^ 2 =
      ρ ((initialPolynomial u).eval₂ φ x)) :
    ρ ((liftedPolynomial u t).eval₂ φ x) = ρ ((initialPolynomial u).eval₂ φ x) := by
  unfold liftedPolynomial
  rw [eval_normalized _ _ (ternaryH_monic.pow t) φ x (by simpa only [eval₂_pow] using hx)]
  exact iterate_residue ρ hi _

theorem lifted_eval_zero_residue (φ : A →+* O) (ρ : O →+* K)
    (u : A) (hu : 2 * u = 1) (q : O) (t : ℕ)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (x : O) (hx : ρ x = 0) : (liftedPolynomial u t).eval₂ φ x = 1 := by
  have hH := eval_H_nilpotent φ ρ q t hker hq x (Or.inl hx)
  have hi : ρ ((initialPolynomial u).eval₂ φ x) = 1 := by
    rw [eval_initialPolynomial, map_initialValue, hx]
    exact initialValue_zero _ (mapped_inverse_two ρ (mapped_inverse_two φ hu))
  have he := lifted_eval_idempotent φ u hu t x hH
  have hr := lifted_eval_residue φ ρ u t x hH (by rw [hi]; ring)
  apply idempotent_one_of_residue ρ hker he hq
  exact hr.trans hi

theorem lifted_eval_nonzero_residue (φ : A →+* O) (ρ : O →+* K)
    (u : A) (hu : 2 * u = 1) (q : O) (t : ℕ)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (x : O) (hx : ρ x = 1 ∨ ρ x = 2) : (liftedPolynomial u t).eval₂ φ x = 0 := by
  have hH := eval_H_nilpotent φ ρ q t hker hq x (Or.inr hx)
  have hi : ρ ((initialPolynomial u).eval₂ φ x) = 0 := by
    rw [eval_initialPolynomial, map_initialValue]
    rcases hx with h | h <;> rw [h] <;> simp
  have he := lifted_eval_idempotent φ u hu t x hH
  have hr := lifted_eval_residue φ ρ u t x hH (by rw [hi]; ring)
  apply idempotent_zero_of_residue ρ hker he hq
  exact hr.trans hi

theorem coefficients_indicator [DecidableEq K] (φ : A →+* O) (ρ : O →+* K)
    (u : A) (hu : 2 * u = 1) (q : O) (t : ℕ)
    (hker : ∀ y, ρ y = 0 → q ∣ y) (hq : q ^ t = 0)
    (x : O) (hx : ρ x = 0 ∨ ρ x = 1 ∨ ρ x = 2) :
    (∑ s : Fin t, (coefficients u t s).eval₂ φ x *
      ((ternaryH : A[X]).eval₂ φ x) ^ (s : ℕ)) = if ρ x = 0 then 1 else 0 := by
  rw [← coefficient_eval_sum φ u t x (eval_H_nilpotent φ ρ q t hker hq x hx)]
  by_cases hz : ρ x = 0
  · simp only [hz, ↓reduceIte]
    exact lifted_eval_zero_residue φ ρ u hu q t hker hq x hz
  · simp only [hz, ↓reduceIte]
    apply lifted_eval_nonzero_residue φ ρ u hu q t hker hq x
    exact hx.resolve_left hz

end SubexponentialSAT.SqrtLog.Idempotent

end OAI.Algorithms
