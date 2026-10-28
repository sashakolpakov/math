import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExponentArithmetic

namespace OAI.Algorithms

/-!
# Absorbing the finitely many small variable counts

These are inequalities of real powers and finite maxima.  They establish no
machine execution bound by themselves: a parser or solver must separately be
proved to obey the displayed polynomial/exhaustive-search upper bound.

The variable count is bounded, but the explicit input length remains arbitrary.
The finite-maximum lemmas therefore maximize coefficients and polynomial degrees
in the variable count, while retaining the polynomial dependence on input length.
-/

namespace SubexponentialSAT.SmallInputs

noncomputable section

/-- The exponential part of the claimed time bound, including at zero variables. -/
def savedExponential (n : ℕ) : ℝ := (2 : ℝ) ^ ((9 / 10 : ℝ) * (n : ℝ))

/-- The explicit loss for exhaustive search on variable counts at most `B`. -/
def bruteForceFactor (B : ℕ) : ℝ := (2 : ℝ) ^ ((B : ℝ) / 10)

/-- A polynomial factor in explicit input length, with a safe value at length zero. -/
def inputPolynomial (L d : ℕ) : ℝ := ((L : ℝ) + 1) ^ d

/-- The actual dimension obtained by packing at most `ell` bits into each coordinate. -/
def packedDimension (n ell : ℕ) : ℕ := ⌈(n : ℝ) / (ell : ℝ)⌉₊

@[simp] theorem savedExponential_zero : savedExponential 0 = 1 := by
  simp [savedExponential]

@[simp] theorem bruteForceFactor_zero : bruteForceFactor 0 = 1 := by
  simp [bruteForceFactor]

@[simp] theorem inputPolynomial_zero_length (d : ℕ) : inputPolynomial 0 d = 1 := by
  simp [inputPolynomial]

@[simp] theorem packedDimension_zero (ell : ℕ) : packedDimension 0 ell = 0 := by
  simp [packedDimension]

theorem savedExponential_pos (n : ℕ) : 0 < savedExponential n :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem one_le_savedExponential (n : ℕ) : 1 ≤ savedExponential n := by
  apply Real.one_le_rpow (by norm_num)
  positivity

theorem bruteForceFactor_pos (B : ℕ) : 0 < bruteForceFactor B :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem one_le_bruteForceFactor (B : ℕ) : 1 ≤ bruteForceFactor B := by
  apply Real.one_le_rpow (by norm_num)
  positivity

theorem inputPolynomial_nonneg (L d : ℕ) : 0 ≤ inputPolynomial L d := by
  unfold inputPolynomial
  positivity

theorem one_le_inputPolynomial (L d : ℕ) : 1 ≤ inputPolynomial L d := by
  apply one_le_pow₀
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  linarith

/-- Packing at positive capacity covers every input bit. -/
theorem variables_le_packed_capacity (n : ℕ) {ell : ℕ} (hell : 0 < ell) :
    n ≤ ell * packedDimension n ell := by
  have hellR : (0 : ℝ) < ell := by exact_mod_cast hell
  have hceil : (n : ℝ) / (ell : ℝ) ≤ (packedDimension n ell : ℝ) :=
    Nat.le_ceil _
  have h : (n : ℝ) ≤ (ell : ℝ) * (packedDimension n ell : ℝ) := by
    have := (div_le_iff₀ hellR).mp hceil
    nlinarith
  exact_mod_cast h

/-- Zero packed dimension really means zero bits, provided the capacity is positive. -/
theorem packedDimension_eq_zero_iff {n ell : ℕ} (hell : 0 < ell) :
    packedDimension n ell = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hn := variables_le_packed_capacity n hell
    simpa [h] using hn
  · rintro rfl
    exact packedDimension_zero ell

/-- The strict dimension cutoff implies the manuscript's weaker non-strict bit cutoff. -/
theorem variables_le_threshold {n ell Dstar : ℕ} (hell : 0 < ell)
    (hD : packedDimension n ell < Dstar) : n ≤ ell * Dstar :=
  (variables_le_packed_capacity n hell).trans (Nat.mul_le_mul_left ell hD.le)

/-- Explicit finite-threshold absorption, with the same factor as Section 6.4. -/
theorem bruteForce_le_saved {n B : ℕ} (hn : n ≤ B) :
    (2 : ℝ) ^ (n : ℝ) ≤ bruteForceFactor B * savedExponential n := by
  unfold bruteForceFactor savedExponential
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hnR : (n : ℝ) ≤ B := by exact_mod_cast hn
  nlinarith

/-- The same bound for the natural-number exhaustive-search count. -/
theorem nat_bruteForce_le_saved {n B : ℕ} (hn : n ≤ B) :
    ((2 ^ n : ℕ) : ℝ) ≤ bruteForceFactor B * savedExponential n := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast] using
    bruteForce_le_saved hn

/-- Direct form using the fixed bit capacity and dimension threshold. -/
theorem packed_bruteForce_le_saved {n ell Dstar : ℕ} (hell : 0 < ell)
    (hD : packedDimension n ell < Dstar) :
    ((2 ^ n : ℕ) : ℝ) ≤ bruteForceFactor (ell * Dstar) * savedExponential n :=
  nat_bruteForce_le_saved (variables_le_threshold hell hD)

/-- Exhaustive search multiplied by any nonnegative input-dependent overhead. -/
theorem overhead_bruteForce_le_saved {n B : ℕ} {overhead : ℝ}
    (hn : n ≤ B) (hoverhead : 0 ≤ overhead) :
    overhead * ((2 ^ n : ℕ) : ℝ) ≤
      (overhead * bruteForceFactor B) * savedExponential n := by
  calc
    overhead * ((2 ^ n : ℕ) : ℝ) ≤
        overhead * (bruteForceFactor B * savedExponential n) :=
      mul_le_mul_of_nonneg_left (nat_bruteForce_le_saved hn) hoverhead
    _ = (overhead * bruteForceFactor B) * savedExponential n := by ring

/-- Polynomial time per candidate retains its input-length degree after absorption. -/
theorem polynomial_bruteForce_le_saved {n B L d : ℕ} {a : ℝ}
    (hn : n ≤ B) (ha : 0 ≤ a) :
    a * inputPolynomial L d * ((2 ^ n : ℕ) : ℝ) ≤
      (a * bruteForceFactor B) * inputPolynomial L d * savedExponential n := by
  calc
    a * inputPolynomial L d * ((2 ^ n : ℕ) : ℝ) ≤
        (a * inputPolynomial L d * bruteForceFactor B) * savedExponential n :=
      overhead_bruteForce_le_saved hn (mul_nonneg ha (inputPolynomial_nonneg L d))
    _ = (a * bruteForceFactor B) * inputPolynomial L d * savedExponential n := by ring

/-- Polynomial factors multiply by adding degrees. -/
theorem inputPolynomial_mul (L d e : ℕ) :
    inputPolynomial L d * inputPolynomial L e = inputPolynomial L (d + e) := by
  simp only [inputPolynomial, pow_add]

/-- Increasing the polynomial degree is harmless because the base is at least one. -/
theorem inputPolynomial_mono_degree (L : ℕ) {d e : ℕ} (h : d ≤ e) :
    inputPolynomial L d ≤ inputPolynomial L e := by
  apply pow_le_pow_right₀ _ h
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  linarith

/-- Linear control of variable count by encoding length transfers polynomial overhead. -/
theorem inputPolynomial_of_linear_bound {n L a d : ℕ} (hn : n ≤ a * (L + 1)) :
    inputPolynomial n d ≤ ((a : ℝ) + 1) ^ d * inputPolynomial L d := by
  have hnR : (n : ℝ) ≤ (a : ℝ) * ((L : ℝ) + 1) := by exact_mod_cast hn
  have hbase : (n : ℝ) + 1 ≤ ((a : ℝ) + 1) * ((L : ℝ) + 1) := by
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    nlinarith
  calc
    inputPolynomial n d ≤ (((a : ℝ) + 1) * ((L : ℝ) + 1)) ^ d :=
      pow_le_pow_left₀ (by positivity) hbase d
    _ = ((a : ℝ) + 1) ^ d * inputPolynomial L d := by
      rw [mul_pow]
      rfl

/-- A finite maximum of normalized coefficients. It is positive even at threshold zero. -/
def finiteCoefficient (B : ℕ) (c : ℕ → ℝ) : ℝ :=
  max 1 ((Finset.range (B + 1)).sup' (by simp) fun n => c n / savedExponential n)

/-- Maximum degree across the finite set of small variable counts. -/
def finiteDegree (B : ℕ) (degree : ℕ → ℕ) : ℕ :=
  (Finset.range (B + 1)).sup degree

theorem one_le_finiteCoefficient (B : ℕ) (c : ℕ → ℝ) :
    1 ≤ finiteCoefficient B c := le_max_left _ _

theorem finiteCoefficient_pos (B : ℕ) (c : ℕ → ℝ) :
    0 < finiteCoefficient B c := lt_of_lt_of_le (by norm_num) (one_le_finiteCoefficient B c)

/-- The finite maximum dominates each normalized coefficient in its range. -/
theorem coefficient_le_finiteCoefficient {B n : ℕ} (c : ℕ → ℝ) (hn : n ≤ B) :
    c n ≤ finiteCoefficient B c * savedExponential n := by
  apply (div_le_iff₀ (savedExponential_pos n)).mp
  have hmem : n ∈ Finset.range (B + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  exact (Finset.le_sup' (fun m => c m / savedExponential m) hmem).trans (le_max_right _ _)

theorem degree_le_finiteDegree {B n : ℕ} (degree : ℕ → ℕ) (hn : n ≤ B) :
    degree n ≤ finiteDegree B degree :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))

/-- Even when each small variable count has its own polynomial degree and coefficient,
finite maxima give one positive coefficient and one degree for all explicit input lengths. -/
theorem finite_polynomial_family_le_saved {B n L : ℕ}
    (c : ℕ → ℝ) (degree : ℕ → ℕ) (hn : n ≤ B) :
    c n * inputPolynomial L (degree n) ≤
      finiteCoefficient B c * inputPolynomial L (finiteDegree B degree) * savedExponential n := by
  calc
    c n * inputPolynomial L (degree n) ≤
        (finiteCoefficient B c * savedExponential n) * inputPolynomial L (degree n) :=
      mul_le_mul_of_nonneg_right (coefficient_le_finiteCoefficient c hn)
        (inputPolynomial_nonneg L (degree n))
    _ ≤ (finiteCoefficient B c * savedExponential n) *
        inputPolynomial L (finiteDegree B degree) :=
      mul_le_mul_of_nonneg_left
        (inputPolynomial_mono_degree L (degree_le_finiteDegree degree hn))
        (mul_nonneg (finiteCoefficient_pos B c).le (savedExponential_pos n).le)
    _ = finiteCoefficient B c * inputPolynomial L (finiteDegree B degree) *
        savedExponential n := by ring

/-- A genuine uniform bound for a finite family of input-length polynomials.
The coefficient and degree are chosen before both the input length and the
particular small variable count. -/
theorem exists_uniform_finite_polynomial_bound (B : ℕ)
    (c : ℕ → ℝ) (degree : ℕ → ℕ) :
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ n ≤ B, ∀ L,
      c n * inputPolynomial L (degree n) ≤ C * inputPolynomial L d * savedExponential n := by
  exact ⟨finiteCoefficient B c, finiteDegree B degree,
    finiteCoefficient_pos B c, fun _ hn _ => finite_polynomial_family_le_saved c degree hn⟩

/-- At threshold zero, the finite maxima include exactly the zero-variable case. -/
@[simp] theorem finiteDegree_zero (degree : ℕ → ℕ) : finiteDegree 0 degree = degree 0 := by
  simp [finiteDegree]

@[simp] theorem finiteCoefficient_zero (c : ℕ → ℝ) : finiteCoefficient 0 c = max 1 (c 0) := by
  simp [finiteCoefficient]

/-- Parsing may be charged additively without changing the common polynomial degree.
The numerical coefficients are fixed independently of the input. -/
theorem parsing_plus_bruteForce_le_saved {n B L d : ℕ} {parsing search : ℝ}
    (hn : n ≤ B) (hp : 0 ≤ parsing) (hs : 0 ≤ search) :
    parsing * inputPolynomial L d +
        search * inputPolynomial L d * ((2 ^ n : ℕ) : ℝ) ≤
      (parsing + search * bruteForceFactor B) * inputPolynomial L d * savedExponential n := by
  have hparse : parsing * inputPolynomial L d ≤
      parsing * inputPolynomial L d * savedExponential n := by
    exact le_mul_of_one_le_right (mul_nonneg hp (inputPolynomial_nonneg L d))
      (one_le_savedExponential n)
  have hsearch := polynomial_bruteForce_le_saved (L := L) (d := d) hn hs
  calc
    parsing * inputPolynomial L d + search * inputPolynomial L d * ((2 ^ n : ℕ) : ℝ) ≤
        parsing * inputPolynomial L d * savedExponential n +
          (search * bruteForceFactor B) * inputPolynomial L d * savedExponential n :=
      add_le_add hparse hsearch
    _ = (parsing + search * bruteForceFactor B) * inputPolynomial L d * savedExponential n := by ring

end

end SubexponentialSAT.SmallInputs

end OAI.Algorithms
