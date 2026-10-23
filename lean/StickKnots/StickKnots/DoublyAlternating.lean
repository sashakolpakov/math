import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# An explicit factorial-scale family of doubly alternating permutations

This file gives an elementary replacement for the RSK step in the long-word
lower bound.  For `n = 4 * k`, four independent permutations of `Fin k`
produce a permutation of `Fin n` which is down--up both before and after
inversion.  The construction is injective, so it supplies `(k!)^4` such
permutations.

The indexing convention is explicit: a descent at zero-based index `i` means
the one-based position `i + 1` is a descent.  Thus down--up means precisely
that the zero-based descent indices are even.
-/

namespace StickKnots

open Equiv
open Filter Asymptotics

/-- The left endpoint of the adjacent pair indexed by `i : Fin (n - 1)`. -/
def adjacentLeft {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i, by omega⟩

/-- The right endpoint of the adjacent pair indexed by `i : Fin (n - 1)`. -/
def adjacentRight {n : ℕ} (i : Fin (n - 1)) : Fin n :=
  ⟨i + 1, by omega⟩

/-- `w` is down--up in one-based notation: `w₁ > w₂ < w₃ > ⋯`.
Equivalently, its zero-based descent indices are exactly the even indices. -/
def IsDownUp {n : ℕ} (w : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin (n - 1),
    (w (adjacentLeft i) > w (adjacentRight i)) ↔ Even (i : ℕ)

/-- A permutation is doubly down--up when it and its inverse are down--up. -/
def IsDoublyDownUp {n : ℕ} (w : Equiv.Perm (Fin n)) : Prop :=
  IsDownUp w ∧ IsDownUp w⁻¹

/-- Coordinates for `Fin (4*k)`: upper/lower half, rank within the
half-and-parity class, and zero-based parity. -/
abbrev QuarterCoordinates (k : ℕ) := Fin 2 × (Fin k × Fin 2)

/-- The standard mixed-radix equivalence
`(half, rank, parity) ↦ half * (2*k) + 2*rank + parity`. -/
def quarterCoordinatesEquiv (k : ℕ) : QuarterCoordinates k ≃ Fin (4 * k) :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans <|
    finProdFinEquiv.trans <| finCongr (by omega)

@[simp]
theorem quarterCoordinatesEquiv_val (k : ℕ) (x : QuarterCoordinates k) :
    (quarterCoordinatesEquiv k x : ℕ) =
      (x.1 : ℕ) * (2 * k) + 2 * (x.2.1 : ℕ) + (x.2.2 : ℕ) := by
  simp [quarterCoordinatesEquiv, finProdFinEquiv]
  ring

/-- Four independent permutations of `Fin k`, indexed by half and parity. -/
abbrev QuarterPermutations (k : ℕ) := Fin 2 → Fin 2 → Equiv.Perm (Fin k)

/-- Coordinate form of the construction.  It exchanges position parity with
value half and position half with value parity, reversing both bits; the rank
inside each of the four classes is independently permuted.

In symbols, `(h,r,p) ↦ (1-p, σ h p r, 1-h)`. -/
def quarterCoordinatePerm {k : ℕ} (σ : QuarterPermutations k) :
    Equiv.Perm (QuarterCoordinates k) where
  toFun x := (x.2.2.rev, (σ x.1 x.2.2 x.2.1, x.1.rev))
  invFun x := (x.2.2.rev, ((σ x.2.2.rev x.1.rev).symm x.2.1, x.1.rev))
  left_inv x := by simp
  right_inv x := by simp

/-- The resulting permutation of `Fin (4*k)`. -/
def quarterFamilyPerm {k : ℕ} (σ : QuarterPermutations k) :
    Equiv.Perm (Fin (4 * k)) :=
  (quarterCoordinatesEquiv k).symm.trans <|
    (quarterCoordinatePerm σ).trans (quarterCoordinatesEquiv k)

@[simp]
theorem quarterFamilyPerm_apply_coordinates {k : ℕ} (σ : QuarterPermutations k)
    (x : QuarterCoordinates k) :
    quarterFamilyPerm σ (quarterCoordinatesEquiv k x) =
      quarterCoordinatesEquiv k (quarterCoordinatePerm σ x) := by
  simp [quarterFamilyPerm]

/-- The image lies in the upper half exactly when the input position is even
in zero-based indexing (equivalently, odd in one-based indexing). -/
theorem quarterFamilyPerm_upperHalf_iff_even {k : ℕ} (σ : QuarterPermutations k)
    (x : Fin (4 * k)) :
    2 * k ≤ (quarterFamilyPerm σ x : ℕ) ↔ Even (x : ℕ) := by
  let c := (quarterCoordinatesEquiv k).symm x
  have hx : x = quarterCoordinatesEquiv k c := by simp [c]
  rw [hx, quarterFamilyPerm_apply_coordinates]
  rcases c with ⟨h, r, p⟩
  simp only [quarterCoordinatesEquiv_val]
  fin_cases h <;> fin_cases p <;>
    simp [quarterCoordinatePerm, Fin.rev, Nat.even_iff] <;>
    omega

/-- Reindexing and inversion of the four internal permutations which describes
the inverse of `quarterFamilyPerm σ`. -/
def quarterInversePermutations {k : ℕ} (σ : QuarterPermutations k) :
    QuarterPermutations k :=
  fun h p ↦ (σ p.rev h.rev).symm

theorem quarterFamilyPerm_symm {k : ℕ} (σ : QuarterPermutations k) :
    (quarterFamilyPerm σ).symm = quarterFamilyPerm (quarterInversePermutations σ) := by
  apply Equiv.ext
  intro x
  let c := (quarterCoordinatesEquiv k).symm x
  have hx : x = quarterCoordinatesEquiv k c := by simp [c]
  rw [hx]
  rcases c with ⟨h, r, p⟩
  simp [quarterFamilyPerm, quarterCoordinatePerm, quarterInversePermutations]

/-- The same upper-half/even-position law holds for the inverse permutation. -/
theorem quarterFamilyPerm_symm_upperHalf_iff_even {k : ℕ} (σ : QuarterPermutations k)
    (x : Fin (4 * k)) :
    2 * k ≤ ((quarterFamilyPerm σ).symm x : ℕ) ↔ Even (x : ℕ) := by
  rw [quarterFamilyPerm_symm]
  exact quarterFamilyPerm_upperHalf_iff_even (quarterInversePermutations σ) x

/-- Separating the values in even and odd zero-based positions into the upper
and lower halves forces the down--up inequalities. -/
theorem isDownUp_of_upperHalf_iff_even {k : ℕ} {w : Equiv.Perm (Fin (4 * k))}
    (hHalf : ∀ x, 2 * k ≤ (w x : ℕ) ↔ Even (x : ℕ)) :
    IsDownUp w := by
  intro i
  constructor
  · intro hDescent
    by_contra hEven
    have hLeftLow : (w (adjacentLeft i) : ℕ) < 2 * k := by
      apply lt_of_not_ge
      intro hGe
      apply hEven
      simpa [adjacentLeft] using (hHalf _).mp hGe
    have hRightHigh : 2 * k ≤ (w (adjacentRight i) : ℕ) := by
      rw [hHalf]
      have hOdd : Odd (i : ℕ) := Nat.not_even_iff_odd.mp hEven
      simpa [adjacentRight] using hOdd.add_one
    change (w (adjacentRight i) : ℕ) < (w (adjacentLeft i) : ℕ) at hDescent
    omega
  · intro hEven
    have hLeftHigh : 2 * k ≤ (w (adjacentLeft i) : ℕ) := by
      rw [hHalf]
      simpa [adjacentLeft] using hEven
    have hRightLow : (w (adjacentRight i) : ℕ) < 2 * k := by
      apply lt_of_not_ge
      intro hGe
      have hRightEven : Even (adjacentRight i : ℕ) := (hHalf _).mp hGe
      have hOdd : Odd ((i : ℕ) + 1) := hEven.add_one
      exact (Nat.not_even_iff_odd.mpr hOdd) (by simpa [adjacentRight] using hRightEven)
    change (w (adjacentRight i) : ℕ) < (w (adjacentLeft i) : ℕ)
    omega

theorem quarterFamilyPerm_isDownUp {k : ℕ} (σ : QuarterPermutations k) :
    IsDownUp (quarterFamilyPerm σ) :=
  isDownUp_of_upperHalf_iff_even (quarterFamilyPerm_upperHalf_iff_even σ)

theorem quarterFamilyPerm_symm_isDownUp {k : ℕ} (σ : QuarterPermutations k) :
    IsDownUp (quarterFamilyPerm σ).symm :=
  isDownUp_of_upperHalf_iff_even (quarterFamilyPerm_symm_upperHalf_iff_even σ)

/-- Every member of the quarter-family is doubly down--up. -/
theorem quarterFamilyPerm_isDoublyDownUp {k : ℕ} (σ : QuarterPermutations k) :
    IsDoublyDownUp (quarterFamilyPerm σ) :=
  ⟨quarterFamilyPerm_isDownUp σ, quarterFamilyPerm_symm_isDownUp σ⟩

/-- The finite type of doubly down--up permutations. -/
def DoublyDownUpPerm (n : ℕ) :=
  {w : Equiv.Perm (Fin n) // IsDoublyDownUp w}

noncomputable instance (n : ℕ) : Fintype (DoublyDownUpPerm n) :=
  letI : Finite (DoublyDownUpPerm n) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  Fintype.ofFinite _

/-- The four internal permutations can be recovered from the constructed
permutation. -/
theorem quarterCoordinatePerm_injective {k : ℕ} :
    Function.Injective (quarterCoordinatePerm :
      QuarterPermutations k → Equiv.Perm (QuarterCoordinates k)) := by
  intro σ τ hστ
  funext h p
  apply Equiv.ext
  intro r
  have hApply := Equiv.congr_fun hστ (h, (r, p))
  exact congrArg (fun x ↦ x.2.1) hApply

theorem quarterFamilyPerm_injective {k : ℕ} :
    Function.Injective (quarterFamilyPerm :
      QuarterPermutations k → Equiv.Perm (Fin (4 * k))) := by
  intro σ τ hστ
  apply quarterCoordinatePerm_injective
  apply Equiv.ext
  intro c
  have hApply := Equiv.congr_fun hστ (quarterCoordinatesEquiv k c)
  apply (quarterCoordinatesEquiv k).injective
  simpa [quarterFamilyPerm] using hApply

/-- The quarter-family as a map into the subtype of doubly down--up
permutations. -/
def quarterFamilyDoublyDownUp {k : ℕ} (σ : QuarterPermutations k) :
    DoublyDownUpPerm (4 * k) :=
  ⟨quarterFamilyPerm σ, quarterFamilyPerm_isDoublyDownUp σ⟩

theorem quarterFamilyDoublyDownUp_injective {k : ℕ} :
    Function.Injective (quarterFamilyDoublyDownUp :
      QuarterPermutations k → DoublyDownUpPerm (4 * k)) := by
  intro σ τ h
  exact quarterFamilyPerm_injective (congrArg Subtype.val h)

/-- There are exactly `(k!)^4` choices of the four internal permutations. -/
theorem card_quarterPermutations (k : ℕ) :
    Fintype.card (QuarterPermutations k) = k.factorial ^ 4 := by
  simp [QuarterPermutations, Fintype.card_perm, pow_succ]
  ring

/-- Elementary factorial-scale lower bound for doubly alternating
permutations at sizes divisible by four. -/
theorem factorial_fourth_power_le_card_doublyDownUp (k : ℕ) :
    k.factorial ^ 4 ≤ Fintype.card (DoublyDownUpPerm (4 * k)) := by
  rw [← card_quarterPermutations]
  exact Fintype.card_le_of_injective quarterFamilyDoublyDownUp
    quarterFamilyDoublyDownUp_injective

/-- The endpoint-permutation loss is an ordinary finite pigeonhole argument,
once a finite word type and its endpoint map have been defined.  No braid or
Garside theory is used in this lemma. -/
theorem exists_endpointPermutation_fiber {n : ℕ} {W : Type*} [Fintype W]
    (endpoint : W → Equiv.Perm (Fin n)) :
    ∃ u : Equiv.Perm (Fin n),
      Fintype.card W ≤ n.factorial * (Finset.univ.filter fun w ↦ endpoint w = u).card := by
  classical
  let A := Fintype.card W
  let B := n.factorial
  have hB : 0 < B := Nat.factorial_pos n
  by_cases hA : A = 0
  · exact ⟨1, by simp [A, hA]⟩
  · let c := A ⌈/⌉ B
    have hAc : A ≤ B * c := by
      exact (ceilDiv_le_iff_le_mul hB).1 le_rfl
    have hcpos : 0 < c := by
      by_contra hc
      have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
      rw [hc0, mul_zero] at hAc
      omega
    have hPred : B * (c - 1) < A := by
      by_contra h
      have hWrong : c ≤ c - 1 := (ceilDiv_le_iff_le_mul hB).2 (Nat.le_of_not_gt h)
      omega
    have hPigeon : Fintype.card (Equiv.Perm (Fin n)) * (c - 1) < Fintype.card W := by
      simpa [A, B, Fintype.card_perm] using hPred
    obtain ⟨u, hu⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card endpoint hPigeon
    refine ⟨u, ?_⟩
    have hcFiber : c ≤ (Finset.univ.filter fun w ↦ endpoint w = u).card := by omega
    calc
      Fintype.card W = A := rfl
      _ ≤ B * c := hAc
      _ ≤ B * (Finset.univ.filter fun w ↦ endpoint w = u).card :=
        Nat.mul_le_mul_left B hcFiber
      _ = n.factorial * (Finset.univ.filter fun w ↦ endpoint w = u).card := rfl

/-- Applying the preceding pigeonhole lemma to `q`-letter words in the
doubly down--up alphabet.  The only count used is the explicit `(k!)^4`
subfamily. -/
theorem exists_doublyDownUp_word_endpoint_fiber (k q : ℕ)
    (endpoint : (Fin q → DoublyDownUpPerm (4 * k)) → Equiv.Perm (Fin (4 * k))) :
    ∃ u : Equiv.Perm (Fin (4 * k)),
      (k.factorial ^ 4) ^ q ≤
        (4 * k).factorial * (Finset.univ.filter fun w ↦ endpoint w = u).card := by
  obtain ⟨u, hu⟩ := exists_endpointPermutation_fiber endpoint
  refine ⟨u, ?_⟩
  calc
    (k.factorial ^ 4) ^ q ≤
        Fintype.card (DoublyDownUpPerm (4 * k)) ^ q := by
      gcongr
      exact factorial_fourth_power_le_card_doublyDownUp k
    _ = Fintype.card (Fin q → DoublyDownUpPerm (4 * k)) := by
      rw [Fintype.card_pi_const]
    _ ≤ (4 * k).factorial * (Finset.univ.filter fun w ↦ endpoint w = u).card := hu

/-- The opposite, tautological bound: doubly down--up permutations are a
subtype of all permutations. -/
theorem card_doublyDownUp_le_factorial (n : ℕ) :
    Fintype.card (DoublyDownUpPerm n) ≤ n.factorial := by
  calc
    Fintype.card (DoublyDownUpPerm n) ≤
        Fintype.card (Equiv.Perm (Fin n)) :=
      Fintype.card_le_of_injective (fun w : DoublyDownUpPerm n ↦ w.1)
        Subtype.val_injective
    _ = n.factorial := by simp [Fintype.card_perm]

/-- Split `(4*k)!` into three binomial coefficients and four copies of `k!`. -/
theorem factorial_four_mul_decomposition (k : ℕ) :
    (4 * k).factorial =
      (4 * k).choose k * (3 * k).choose k * (2 * k).choose k * k.factorial ^ 4 := by
  have h4 := Nat.choose_mul_factorial_mul_factorial (n := 4 * k) (k := k) (by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (n := 2 * k) (k := k) (by omega)
  simp only [show 4 * k - k = 3 * k by omega] at h4
  simp only [show 3 * k - k = 2 * k by omega] at h3
  simp only [show 2 * k - k = k by omega] at h2
  rw [← h4, ← h3, ← h2]
  ring

/-- Exact exponential-loss estimate.  In particular `(k!)^4` differs from
`(4*k)!` by at most an exponential factor, which is the only asymptotic fact
the lower-bound construction needs. -/
theorem factorial_four_mul_le_two_pow_mul_quarter_factorials (k : ℕ) :
    (4 * k).factorial ≤ 2 ^ (9 * k) * k.factorial ^ 4 := by
  rw [factorial_four_mul_decomposition]
  apply Nat.mul_le_mul_right (k.factorial ^ 4)
  calc
    (4 * k).choose k * (3 * k).choose k * (2 * k).choose k ≤
        2 ^ (4 * k) * 2 ^ (3 * k) * 2 ^ (2 * k) := by
      gcongr <;> exact Nat.choose_le_two_pow _ _
    _ = 2 ^ (9 * k) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

/-- Logarithmic form of the exponential-loss estimate. -/
theorem log_factorial_four_mul_le_log_quarter_factorials (k : ℕ) :
    Real.log ((4 * k).factorial : ℝ) ≤
      (9 * k : ℕ) * Real.log 2 + 4 * Real.log (k.factorial : ℝ) := by
  have hNat := factorial_four_mul_le_two_pow_mul_quarter_factorials k
  have hReal : ((4 * k).factorial : ℝ) ≤
      (2 : ℝ) ^ (9 * k) * (k.factorial : ℝ) ^ 4 := by
    exact_mod_cast hNat
  have hLog := Real.log_le_log (by positivity : (0 : ℝ) < ((4 * k).factorial : ℝ)) hReal
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hLog
  norm_num at hLog ⊢
  simpa [Nat.cast_mul] using hLog

/-- Exact logarithmic sandwich.  It states, without asymptotic notation, that
the logarithm of the doubly down--up count at `n = 4*k` differs from
`log((4*k)!)` by at most a constant times `k`. -/
theorem log_card_doublyDownUp_sandwich (k : ℕ) :
    Real.log ((4 * k).factorial : ℝ) - (9 * k : ℕ) * Real.log 2 ≤
        Real.log (Fintype.card (DoublyDownUpPerm (4 * k)) : ℝ) ∧
      Real.log (Fintype.card (DoublyDownUpPerm (4 * k)) : ℝ) ≤
        Real.log ((4 * k).factorial : ℝ) := by
  have hLowerNat := factorial_fourth_power_le_card_doublyDownUp k
  have hLowerReal : (k.factorial : ℝ) ^ 4 ≤
      (Fintype.card (DoublyDownUpPerm (4 * k)) : ℝ) := by
    exact_mod_cast hLowerNat
  have hLowerLog := Real.log_le_log (by positivity : (0 : ℝ) < (k.factorial : ℝ) ^ 4)
    hLowerReal
  rw [Real.log_pow] at hLowerLog
  norm_num at hLowerLog
  have hUpperNat := card_doublyDownUp_le_factorial (4 * k)
  have hUpperReal : (Fintype.card (DoublyDownUpPerm (4 * k)) : ℝ) ≤
      ((4 * k).factorial : ℝ) := by
    exact_mod_cast hUpperNat
  have hCardPosNat : 0 < Fintype.card (DoublyDownUpPerm (4 * k)) := by
    exact lt_of_lt_of_le (by positivity) hLowerNat
  have hUpperLog := Real.log_le_log (by exact_mod_cast hCardPosNat) hUpperReal
  constructor
  · linarith [log_factorial_four_mul_le_log_quarter_factorials k]
  · exact hUpperLog

/-- Asymptotic packaging of the exact sandwich: along multiples of four, the
logarithmic deficit from the full factorial count is `O(k)`. -/
theorem log_doublyDownUp_deficit_isBigO :
    (fun k : ℕ ↦ Real.log ((4 * k).factorial : ℝ) -
        Real.log (Fintype.card (DoublyDownUpPerm (4 * k)) : ℝ)) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ)) := by
  apply IsBigO.of_bound (9 * Real.log 2)
  filter_upwards with k
  have hBounds := log_card_doublyDownUp_sandwich k
  have hNonneg : 0 ≤ Real.log ((4 * k).factorial : ℝ) -
      Real.log (Fintype.card (DoublyDownUpPerm (4 * k)) : ℝ) := by
    linarith [hBounds.2]
  rw [Real.norm_eq_abs, abs_of_nonneg hNonneg, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg k)]
  norm_num [Nat.cast_mul] at hBounds ⊢
  linarith [hBounds.1]

end StickKnots
