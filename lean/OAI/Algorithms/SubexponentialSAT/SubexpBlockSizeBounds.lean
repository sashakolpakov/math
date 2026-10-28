import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Bounding universal-block search parameters by the block size

Only universal-block parameters occur here. In particular, neither the global
coordinate count nor the number of factors is included in the search size.
The clause width occurs as an explicit coefficient in the polynomial bound.
-/

namespace SubexponentialSAT.SubexpBlockSizeBounds

/-- The number of types for the multi-color universal block. -/
def blockSize (r Q Δ : ℕ) : ℕ := r ^ (Q * (Δ + 1))

theorem color_le_blockSize (r Q Δ : ℕ) (hQ : 1 ≤ Q) :
    r ≤ blockSize r Q Δ := by
  apply Nat.le_self_pow
  have hpos : 0 < Q * (Δ + 1) := Nat.mul_pos (by omega) (by omega)
  omega

theorem exponent_lt_blockSize (r Q Δ : ℕ) (hr : 2 ≤ r) :
    Q * (Δ + 1) < blockSize r Q Δ := by
  exact Nat.lt_pow_self (by omega)

theorem position_lt_blockSize (r Q Δ : ℕ) (hr : 2 ≤ r) :
    Q < blockSize r Q Δ := by
  have h := exponent_lt_blockSize r Q Δ hr
  nlinarith

theorem slot_lt_blockSize (r Q Δ : ℕ) (hr : 2 ≤ r) (hQ : 1 ≤ Q) :
    Δ < blockSize r Q Δ := by
  have h := exponent_lt_blockSize r Q Δ hr
  nlinarith

/-- All varying finite-search parameters are at most the actual type count. -/
structure Bounds (N Q Δ r p R : ℕ) : Prop where
  positive : 0 < N
  color_le : r ≤ N
  position_le : Q ≤ N
  slot_le : Δ ≤ N
  prime_le : p ≤ N
  degree_le : R ≤ N
  extension_le : p ^ 4 ≤ N
  bitlog_le : Nat.log2 p ≤ N

/-- The quartic relation even gives `p^4 ≤ N`, stronger than `p^4 ≤ N+1`.
No lower bound on `Δ` is needed for these estimates. -/
theorem bounds (N Q Δ r p R : ℕ)
    (hN : N = blockSize r Q Δ) (hr : 2 ≤ r) (hQ : 1 ≤ Q)
    (_hp : 2 ≤ p) (hquartic : Q = p ^ 4 - 1) (hR : R ≤ Q) :
    Bounds N Q Δ r p R := by
  have hc : r ≤ N := by simpa only [hN] using color_le_blockSize r Q Δ hQ
  have hq : Q < N := by simpa only [hN] using position_lt_blockSize r Q Δ hr
  have hd : Δ < N := by simpa only [hN] using slot_lt_blockSize r Q Δ hr hQ
  have hp4 : p ≤ p ^ 4 := Nat.le_self_pow (by decide) p
  have hfield : p ^ 4 ≤ N := by omega
  have hpN : p ≤ N := hp4.trans hfield
  exact ⟨by omega, hc, hq.le, hd.le, hpN, hR.trans hq.le,
    hfield, (Nat.log2_le_self p).trans hpN⟩

/-- Specialization to the actual quartic expression for `Q`. -/
theorem quartic_schedule_bounds (r p Δ R : ℕ) (hr : 2 ≤ r) (hp : 2 ≤ p)
    (hR : R ≤ p ^ 4 - 1) :
    Bounds (blockSize r (p ^ 4 - 1) Δ) (p ^ 4 - 1) Δ r p R := by
  have hp4 : p ≤ p ^ 4 := Nat.le_self_pow (by decide) p
  exact bounds _ _ _ _ _ _ rfl hr (by omega) hp rfl hR

namespace Bounds

variable {N Q Δ r p R : ℕ} (h : Bounds N Q Δ r p R)

include h

theorem extension_le_succ : p ^ 4 ≤ N + 1 := h.extension_le.trans (Nat.le_succ N)

theorem log_le : Nat.log 2 p ≤ N := (Nat.log_le_self 2 p).trans h.prime_le

theorem bitwidth_le : Nat.log2 p + 1 ≤ N + 1 := Nat.add_le_add_right h.bitlog_le 1

/-- One matrix formed by stacking the local slot constraints has at most `N^2` rows. -/
theorem local_rows_le_sq (rows : ℕ) (hrows : rows ≤ Δ * N) : rows ≤ N ^ 2 := by
  calc
    rows ≤ Δ * N := hrows
    _ ≤ N * N := Nat.mul_le_mul_right N h.slot_le
    _ = N ^ 2 := by ring

/-- Point/color/slot constraints, including their coordinate entries. -/
theorem constraint_count_le : Q * r * Δ * N ≤ N ^ 4 := by
  calc
    Q * r * Δ * N ≤ N * N * N * N :=
      Nat.mul_le_mul_right N (Nat.mul_le_mul (Nat.mul_le_mul h.position_le h.color_le) h.slot_le)
    _ = N ^ 4 := by ring

/-- A dense matrix entry count per local stacked constraint problem. -/
theorem local_matrix_entries_le (rows cols : ℕ)
    (hrows : rows ≤ Δ * N) (hcols : cols ≤ N) : rows * cols ≤ N ^ 3 := by
  calc
    rows * cols ≤ N ^ 2 * N := Nat.mul_le_mul (h.local_rows_le_sq rows hrows) hcols
    _ = N ^ 3 := by ring

end Bounds

/-- A single scalar size for universal-block construction/search. `k` is
explicit and fixed before varying the input; there is no global `D` or `m`. -/
def parameterSize (N Q Δ r p R k : ℕ) : ℕ :=
  1 + N + Q + Δ + r + p + R + p ^ 4 + Nat.log2 p + k

theorem parameterSize_le {N Q Δ r p R : ℕ} (h : Bounds N Q Δ r p R) (k : ℕ) :
    parameterSize N Q Δ r p R k ≤ (k + 9) * (N + 1) := by
  have hc := h.color_le
  have hq := h.position_le
  have hd := h.slot_le
  have hp := h.prime_le
  have hR := h.degree_le
  have hf := h.extension_le
  have hb := h.bitlog_le
  dsimp [parameterSize]
  nlinarith

/-- Every fixed polynomial in the universal parameters is a fixed polynomial in `N`. -/
theorem parameterSize_pow_le {N Q Δ r p R : ℕ}
    (h : Bounds N Q Δ r p R) (k q : ℕ) :
    parameterSize N Q Δ r p R k ^ q ≤ (k + 9) ^ q * (N + 1) ^ q := by
  simpa only [mul_pow] using Nat.pow_le_pow_left (parameterSize_le h k) q

theorem polynomial_exponent_le {N Q Δ r p R : ℕ}
    (h : Bounds N Q Δ r p R) (k C q : ℕ) :
    C * parameterSize N Q Δ r p R k ^ q ≤
      (C * (k + 9) ^ q) * (N + 1) ^ q := by
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left C (parameterSize_pow_le h k q)

/-- A direct interface for any independently proved finite-search exponent bound. -/
theorem finite_search_exponent_le {N Q Δ r p R E : ℕ}
    (h : Bounds N Q Δ r p R) (k C q : ℕ)
    (hE : E ≤ C * parameterSize N Q Δ r p R k ^ q) :
    E ≤ (C * (k + 9) ^ q) * (N + 1) ^ q :=
  hE.trans (polynomial_exponent_le h k C q)

theorem exp2_polynomial_le {N Q Δ r p R : ℕ}
    (h : Bounds N Q Δ r p R) (k C q : ℕ) :
    2 ^ (C * parameterSize N Q Δ r p R k ^ q) ≤
      2 ^ ((C * (k + 9) ^ q) * (N + 1) ^ q) := by
  exact Nat.pow_le_pow_right (by decide) (polynomial_exponent_le h k C q)

/-- The alphabet, including a quartic extension alphabet, admits a very loose
`N`-bit index. Useful when replacing a finite alphabet power by a base-two power. -/
theorem alphabet_le_two_pow {N q : ℕ} (hq : q ≤ N) : q ≤ 2 ^ N :=
  hq.trans (Nat.lt_two_pow_self.le)

theorem alphabet_pow_le {N q t : ℕ} (hq : q ≤ N) : q ^ t ≤ 2 ^ (N * t) := by
  calc
    q ^ t ≤ (2 ^ N) ^ t := Nat.pow_le_pow_left (alphabet_le_two_pow hq) t
    _ = 2 ^ (N * t) := (pow_mul 2 N t).symm

end SubexponentialSAT.SubexpBlockSizeBounds

end OAI.Algorithms
