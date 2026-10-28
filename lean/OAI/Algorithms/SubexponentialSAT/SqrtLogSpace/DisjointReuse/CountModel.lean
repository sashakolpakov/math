import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.ExecCNF
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Size

/-! Data for the exact-counting statement, corresponding to source lines 45–77.
The primitive execution and space obligations are separate from these data definitions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse

private theorem digits_two_eq_map_toNat (n : ℕ) :
    Nat.digits 2 n = n.bits.map Bool.toNat := by
  rw [Nat.digits_two_eq_bits]
  induction n.bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp_all

/-- Raw clauses retain order and repetitions on all declared variables. -/
abbrev RawCNF (n : ℕ) := ExecCNF.Formula (SAT.Literal (Fin n))

/-- Count every assignment on the declared ambient variable type. -/
def rawCount {n : ℕ} (F : RawCNF n) : ℕ := SAT.count (ExecCNF.formulaSet F)

/-- Explicit list framing retains the raw syntax and the declared variable count. -/
def encodeRawCNF {n : ℕ} (F : RawCNF n) : List Bool :=
  Encoding.encodeNat n ++ Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
    (F.map (List.map Encoding.literalCode))

/-- Canonical least-significant-bit-first binary, with a one-bit representation of zero. -/
def binaryNat (n : ℕ) : List Bool := if n = 0 then [false] else n.bits


theorem rawCount_le {n : ℕ} (F : RawCNF n) : rawCount F ≤ 2 ^ n := by
  simpa [rawCount] using SAT.count_le (ExecCNF.formulaSet F)

@[simp] theorem readNat_encodeRawCNF {n : ℕ} (F : RawCNF n) :
    Encoding.readNat (encodeRawCNF F) = some (n,
      Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
        (F.map (List.map Encoding.literalCode))) := by
  simp [encodeRawCNF]

theorem encodeRawCNF_injective {n : ℕ} :
    Function.Injective (encodeRawCNF (n := n)) := by
  intro F G h
  apply (List.map_injective_iff.mpr
    (List.map_injective_iff.mpr Encoding.literalCode_injective))
  apply Encoding.encodeList_injective
    (Encoding.encodeList_injective Encoding.encodeNat_injective)
  exact List.append_cancel_left h

theorem encodeRawCNF_numVariables {n m : ℕ} (F : RawCNF n) (G : RawCNF m)
    (h : encodeRawCNF F = encodeRawCNF G) : n = m := by
  have hr := congrArg (fun bits => (Encoding.readNat bits).map Prod.fst) h
  simpa using hr

@[simp] theorem binaryNat_zero : binaryNat 0 = [false] := rfl

@[simp] theorem binaryNat_decode (n : ℕ) :
    Nat.ofDigits 2 ((binaryNat n).map Bool.toNat) = n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · rw [binaryNat, ite_eq_right hn, ← digits_two_eq_map_toNat]
    exact Nat.ofDigits_digits 2 n

theorem binaryNat_injective : Function.Injective binaryNat := by
  intro n m h
  have hd := congrArg (fun bits => Nat.ofDigits 2 (bits.map Bool.toNat)) h
  simpa using hd

theorem binaryNat_ne_nil (n : ℕ) : binaryNat n ≠ [] := by
  intro h
  have hd := binaryNat_decode n
  rw [h] at hd
  have hn : n = 0 := hd.symm
  simp [hn] at h

/-- Positive binary words have no redundant most-significant zero bit. -/
theorem binaryNat_eq_append_true {n : ℕ} (hn : n ≠ 0) :
    ∃ initialBits : List Bool, binaryNat n = initialBits ++ [true] := by
  revert hn
  induction n using Nat.binaryRecFromOne with
  | zero => intro h; exact (h rfl).elim
  | one => intro _; exact ⟨[], by simp [binaryNat]⟩
  | bit b n hn ih =>
      intro _
      obtain ⟨initialBits, hp⟩ := ih hn
      have hb := Nat.bit_ne_zero b hn
      simp only [binaryNat, ite_eq_right hn] at hp
      refine ⟨b :: initialBits, ?_⟩
      rw [binaryNat, ite_eq_right hb, Nat.bits_append_bit n b (fun h => (hn h).elim), hp]
      rfl

/-- A decoded word with the canonical terminal bit is the specified binary output. -/
theorem eq_binaryNat_of_decode {word : List Bool} {n : ℕ}
    (hd : Nat.ofDigits 2 (word.map Bool.toNat) = n)
    (hc : word = [false] ∨ ∃ initialBits : List Bool, word = initialBits ++ [true]) :
    word = binaryNat n := by
  rcases hc with rfl | ⟨initialBits, rfl⟩
  · have hn : n = 0 := hd.symm
    simp [hn]
  · have hn : n ≠ 0 := by
      intro hz
      have hzero := hd.trans hz
      exact Nat.one_ne_zero (Nat.digits_zero_of_eq_zero (b := 2) (by decide)
        hzero 1 (by simp))
    have hdigits := Nat.digits_ofDigits 2 (by decide)
      ((initialBits ++ [true]).map Bool.toNat)
      (by
        intro digit hmem
        obtain ⟨b, _, rfl⟩ := List.mem_map.mp hmem
        exact Bool.toNat_lt b)
      (by intro h; simp)
    rw [hd] at hdigits
    apply (List.map_injective_iff.mpr (Function.LeftInverse.injective Bool.ofNat_toNat))
    rw [binaryNat, ite_eq_right hn, ← digits_two_eq_map_toNat]
    exact hdigits.symm

theorem binaryNat_length_le {a n : ℕ} (ha : a ≤ 2 ^ n) :
    (binaryNat a).length ≤ n + 1 := by
  by_cases hzero : a = 0
  · simp [binaryNat, hzero]
  · simpa only [binaryNat, ite_eq_right hzero, Nat.size_eq_bits_len, Nat.size_pow] using
      Nat.size_le_size ha

theorem binaryNat_rawCount_length {n : ℕ} (F : RawCNF n) :
    (binaryNat (rawCount F)).length ≤ n + 1 :=
  binaryNat_length_le (rawCount_le F)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse
