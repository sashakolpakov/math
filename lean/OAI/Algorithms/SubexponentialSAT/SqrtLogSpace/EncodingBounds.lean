import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Size

/-! Canonical count words and the conversion from encoded length to declared input size. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem digits_two_eq_map_toNat (a : ℕ) :
    Nat.digits 2 a = a.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction a.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

/-- Least-significant-bit-first binary, retaining one false bit for zero. -/
def countWord (a : ℕ) : List Bool := if a = 0 then [false] else a.bits

@[simp] theorem countWord_zero : countWord 0 = [false] := rfl

@[simp] theorem countWord_decode (a : ℕ) :
    Nat.ofDigits 2 ((countWord a).map Bool.toNat) = a := by
  by_cases h : a = 0
  · subst a
    rfl
  · rw [countWord, ite_eq_right h, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 a

@[simp] theorem countWord_toNat (a : ℕ) : BinaryArithmetic.toNat (countWord a) = a := by
  have h (word : List Bool) :
      BinaryArithmetic.toNat word = Nat.ofDigits 2 (word.map Bool.toNat) := by
    induction word with
    | nil => rfl
    | cons b word ih =>
        cases b <;> simp [BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih,
          Nat.ofDigits]
  rw [h, countWord_decode]

theorem powerWord_countWord (n : ℕ) :
    List.replicate n false ++ [true] = countWord (2 ^ n) := by
  rw [countWord, ite_eq_right (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Nat.bit0_bits _ (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))]
      simpa [List.replicate_succ] using congrArg (List.cons false) ih

theorem countWord_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (countWord a).length ≤ n + 1 := by
  by_cases h : a = 0
  · simp [countWord, h]
  · simpa only [countWord, ite_eq_right h, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

theorem countWord_count_length {n : ℕ} (F : SAT.CNF (Fin n)) :
    (countWord (SAT.count F)).length ≤ n + 1 :=
  countWord_length_le (by simpa using SAT.count_le F)

@[simp] theorem count_empty (n : ℕ) : SAT.count (∅ : SAT.CNF (Fin n)) = 2 ^ n := by
  simp [SAT.count, SAT.satisfyingAssignments, SAT.Assignment]

theorem count_zero_variables (F : SAT.CNF (Fin 0)) :
    SAT.count F = if F = ∅ then 1 else 0 := by
  by_cases hF : F = ∅
  · simp [hF]
  · rw [ite_eq_right hF]
    obtain ⟨C, hC⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have hCempty : C = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro literal _
      exact Fin.elim0 literal.variable
    exact (SAT.count_eq_zero_iff F).mpr
      (SAT.not_satisfiable_of_empty_mem (hCempty ▸ hC))

theorem encoding_le_declaredSize_sq {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) :
    Encoding.formulaBitLength F + 1 ≤ (8 * k + 7) * (n + F.card + 1) ^ 2 := by
  let N := n + F.card + 1
  have hN : N ≤ N ^ 2 := Nat.le_self_pow (by decide) N
  have hsmall : n + 3 + 4 * F.card ≤ 7 * N ^ 2 := by
    have : n + 3 + 4 * F.card ≤ 7 * N := by dsimp [N]; omega
    exact this.trans (Nat.mul_le_mul_left 7 hN)
  have hproduct : (n + 1) * F.card ≤ N ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul
      (show n + 1 ≤ N by dsimp [N]; omega)
      (show F.card ≤ N by dsimp [N]; omega)
  calc
    Encoding.formulaBitLength F + 1 ≤ n + 3 + (4 + (8 * n + 8) * k) * F.card := by
      have h := Encoding.formulaBitLength_upper F hw
      omega
    _ = (n + 3 + 4 * F.card) + 8 * k * ((n + 1) * F.card) := by ring
    _ ≤ 7 * N ^ 2 + 8 * k * N ^ 2 :=
      Nat.add_le_add hsmall (Nat.mul_le_mul_left (8 * k) hproduct)
    _ = (8 * k + 7) * N ^ 2 := by ring

theorem encoding_pow_le_declaredSize {n k : ℕ} (F : SAT.CNF (Fin n))
    (hw : SAT.WidthAtMost k F) (d : ℕ) :
    ((Encoding.formulaBitLength F : ℝ) + 1) ^ d ≤
      ((8 * k + 7 : ℕ) : ℝ) ^ d * ((n + F.card + 1 : ℕ) : ℝ) ^ (2 * d) := by
  have h : (Encoding.formulaBitLength F : ℝ) + 1 ≤
      ((8 * k + 7 : ℕ) : ℝ) * ((n + F.card + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast encoding_le_declaredSize_sq F hw
  calc
    ((Encoding.formulaBitLength F : ℝ) + 1) ^ d ≤
        (((8 * k + 7 : ℕ) : ℝ) * ((n + F.card + 1 : ℕ) : ℝ) ^ 2) ^ d :=
      pow_le_pow_left₀ (by positivity) h d
    _ = _ := by rw [mul_pow, ← pow_mul]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
