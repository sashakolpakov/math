import Mathlib

/-! # Valuation -/

namespace OAI.NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter

noncomputable section

/-! The rationally normalized additive valuation on the fixed p-adic
algebraic closure, constructed from its spectral norm. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

/-- The rational valuation is given by the constant term of the minimal
polynomial, divided by its degree. Its value at zero is unused. -/
def algebraicValuation (x : AlgebraicClosure ℚ_[q]) : ℚ :=
  (Padic.valuation ((minpoly ℚ_[q] x).coeff 0) : ℚ) /
    (minpoly ℚ_[q] x).natDegree

/-- This normalization agrees with the actual p-adic spectral norm. -/
theorem norm_eq_algebraicValuation (x : AlgebraicClosure ℚ_[q]) (hx : x ≠ 0) :
    ‖x‖ = (q : ℝ) ^ (-(algebraicValuation q x : ℝ)) := by
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hc : (minpoly ℚ_[q] x).coeff 0 ≠ 0 :=
    minpoly.coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx
  rw [← PadicAlgCl.spectralNorm_eq,
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul hq]
  congr 1
  simp only [algebraicValuation, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    Int.cast_neg]
  ring

/-- Equality of spectral norms determines the rational valuation. -/
theorem algebraicValuation_eq_of_norm_eq
    (x y : AlgebraicClosure ℚ_[q]) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ‖x‖ = ‖y‖) : algebraicValuation q x = algebraicValuation q y := by
  rw [norm_eq_algebraicValuation q x hx, norm_eq_algebraicValuation q y hy,
    Real.rpow_right_inj (by exact_mod_cast (Fact.out : q.Prime).pos)
      (by exact_mod_cast (Fact.out : q.Prime).ne_one), neg_inj] at h
  exact_mod_cast h

/-- Multiplication is additive for this rational valuation. -/
theorem algebraicValuation_mul
    (x y : AlgebraicClosure ℚ_[q]) (hx : x ≠ 0) (hy : y ≠ 0) :
    algebraicValuation q (x * y) = algebraicValuation q x + algebraicValuation q y := by
  have h := norm_mul x y
  rw [norm_eq_algebraicValuation q (x * y) (mul_ne_zero hx hy),
    norm_eq_algebraicValuation q x hx, norm_eq_algebraicValuation q y hy,
    ← Real.rpow_add (by exact_mod_cast (Fact.out : q.Prime).pos),
    Real.rpow_right_inj (by exact_mod_cast (Fact.out : q.Prime).pos)
      (by exact_mod_cast (Fact.out : q.Prime).ne_one)] at h
  have hc : (algebraicValuation q (x * y) : ℝ) =
      (algebraicValuation q x : ℝ) + (algebraicValuation q y : ℝ) := by linarith
  exact_mod_cast hc

/-- The valuation satisfies the nonarchimedean inequality. -/
theorem algebraicValuation_add
    (x y : AlgebraicClosure ℚ_[q]) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (algebraicValuation q x) (algebraicValuation q y) ≤ algebraicValuation q (x + y) := by
  have hp : 1 < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have h := PadicAlgCl.isNonarchimedean q x y
  rw [norm_eq_algebraicValuation q (x + y) hxy,
    norm_eq_algebraicValuation q x hx, norm_eq_algebraicValuation q y hy] at h
  rcases le_total (algebraicValuation q x) (algebraicValuation q y) with he | he
  · have he' : -(algebraicValuation q y : ℝ) ≤ -(algebraicValuation q x : ℝ) := by
      exact neg_le_neg (by exact_mod_cast he)
    rw [max_eq_left ((Real.rpow_le_rpow_left_iff hp).mpr he'),
      Real.rpow_le_rpow_left_iff hp, neg_le_neg_iff] at h
    rw [min_eq_left he]
    exact_mod_cast h
  · have he' : -(algebraicValuation q x : ℝ) ≤ -(algebraicValuation q y : ℝ) := by
      exact neg_le_neg (by exact_mod_cast he)
    rw [max_eq_right ((Real.rpow_le_rpow_left_iff hp).mpr he'),
      Real.rpow_le_rpow_left_iff hp, neg_le_neg_iff] at h
    rw [min_eq_right he]
    exact_mod_cast h

/-- On the base field the constructed valuation is the usual Padic valuation. -/
theorem algebraicValuation_algebraMap (x : ℚ_[q]) :
    algebraicValuation q (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) x) =
      (Padic.valuation x : ℚ) := by
  simp only [algebraicValuation, minpoly.eq_X_sub_C, Polynomial.coeff_sub,
    Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
    Polynomial.natDegree_X_sub_C, Nat.cast_one, div_one]
  by_cases hx : x = 0
  · simp [hx]
  have h := (Padic.addValuation (p := q)).map_neg x
  rw [Padic.addValuation.apply (neg_ne_zero.mpr hx), Padic.addValuation.apply hx] at h
  exact_mod_cast h

/-- The normalized additive valuation used to instantiate FrobeniusSlope. -/
def canonicalAddValuation : AddValuation (AlgebraicClosure ℚ_[q]) (WithTop ℚ) :=
  AddValuation.of
    (fun x => if x = 0 then ⊤ else (algebraicValuation q x : WithTop ℚ))
    (by simp)
    (by simpa using algebraicValuation_algebraMap q 1)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simpa only [ite_eq_right hx, ite_eq_right hy, ite_eq_right hxy, ← WithTop.coe_min,
        WithTop.coe_le_coe] using algebraicValuation_add q x y hx hy hxy)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [ite_eq_right hx, ite_eq_right hy, ite_eq_right (mul_ne_zero hx hy),
        algebraicValuation_mul q x y hx hy, WithTop.coe_add])

theorem canonicalAddValuation_apply (x : AlgebraicClosure ℚ_[q]) (hx : x ≠ 0) :
    canonicalAddValuation q x = (algebraicValuation q x : WithTop ℚ) := by
  simp [canonicalAddValuation, AddValuation.of_apply, hx]

theorem canonicalAddValuation_q :
    canonicalAddValuation q (q : AlgebraicClosure ℚ_[q]) = (1 : WithTop ℚ) := by
  have hq : (q : AlgebraicClosure ℚ_[q]) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  rw [canonicalAddValuation_apply q _ hq]
  have h := algebraicValuation_algebraMap q (q : ℚ_[q])
  simpa using congrArg (fun x : ℚ => (x : WithTop ℚ)) h

/-- Every embedding of a finite coefficient field preserves this valuation:
its minimal polynomial over the p-adic base field is unchanged. -/
theorem algebraicValuation_embedding
    {L : Type*} [Field L] [Algebra ℚ_[q] L]
    (f g : L →ₐ[ℚ_[q]] AlgebraicClosure ℚ_[q]) (x : L) :
    algebraicValuation q (f x) = algebraicValuation q (g x) := by
  simp only [algebraicValuation, minpoly.algHom_eq f f.injective,
    minpoly.algHom_eq g g.injective]

theorem algebraicValuation_prod
    {I : Type*} (s : Finset I) (f : I → AlgebraicClosure ℚ_[q])
    (hf : ∀ i ∈ s, f i ≠ 0) :
    algebraicValuation q (∏ i ∈ s, f i) = ∑ i ∈ s, algebraicValuation q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using algebraicValuation_algebraMap q 1
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      algebraicValuation_mul q _ _ (hf i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- Restricting coefficients multiplies the determinant valuation by the
coefficient-field degree. This follows from the product over embeddings. -/
theorem valuation_norm
    {L : Type*} [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    (j : L →ₐ[ℚ_[q]] AlgebraicClosure ℚ_[q]) (x : L) (hx : x ≠ 0) :
    (Padic.valuation (Algebra.norm ℚ_[q] x) : ℚ) =
      (Module.finrank ℚ_[q] L : ℚ) * algebraicValuation q (j x) := by
  classical
  rw [← algebraicValuation_algebraMap q (Algebra.norm ℚ_[q] x),
    Algebra.norm_eq_prod_embeddings ℚ_[q] (AlgebraicClosure ℚ_[q]) x,
    algebraicValuation_prod q Finset.univ _ (fun f _ => (map_ne_zero f).mpr hx)]
  simp only [algebraicValuation_embedding q _ j x, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, AlgHom.card]

end

end OAI.NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter
