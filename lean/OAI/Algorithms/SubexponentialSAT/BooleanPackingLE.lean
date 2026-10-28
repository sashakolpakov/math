import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BooleanPacking
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

namespace OAI.Algorithms

/-!
# Little-endian Boolean chunks

The actual materializer writes the first label bit at the first variable
offset. This module supplies the matching numeric embedding, its inverse and
range, and the exact relation to the older most-significant-first encoding.
All reversals use the actual chunk size, including a shorter final chunk.
-/

namespace SubexponentialSAT.BooleanPackingLE

open BinaryArithmetic
open BooleanPacking (Chunk)

/-- The indexed bit of an actual little-endian word is its numeric test bit. -/
theorem testBit_toNat (word : List Bool) (i : ℕ) (hi : i < word.length) :
    (BinaryArithmetic.toNat word).testBit i = word[i] := by
  induction word generalizing i with
  | nil => simp at hi
  | cons bit word ih =>
    cases i with
    | zero =>
      cases bit <;> simp [bitVal, Nat.testBit_zero, Nat.add_mod]
    | succ i =>
      have hdiv : (bitVal bit + 2 * BinaryArithmetic.toNat word) / 2 = BinaryArithmetic.toNat word := by
        cases bit <;> simp [bitVal] ; omega
      rw [Nat.testBit_succ]
      simpa only [toNat_cons, hdiv, List.getElem_cons_succ] using
        ih i (by simpa using hi)

theorem getElem_eq_testBit (word : List Bool) (i : ℕ) (hi : i < word.length) :
    word[i] = (BinaryArithmetic.toNat word).testBit i := (testBit_toNat word i hi).symm

/-- Fixed-width little-endian words are determined by their numeric value.
Leading zeroes are allowed because the two widths agree. -/
theorem word_eq_of_length_value (xs ys : List Bool)
    (hlen : xs.length = ys.length) (hval : BinaryArithmetic.toNat xs = BinaryArithmetic.toNat ys) : xs = ys := by
  apply List.ext_getElem
  · exact hlen
  · intro i hix hiy
    rw [getElem_eq_testBit xs i hix, getElem_eq_testBit ys i hiy, hval]

/-- Missing high bits have their usual value false. -/
theorem testBit_toNat_getD (word : List Bool) (i : ℕ) :
    (BinaryArithmetic.toNat word).testBit i = word[i]?.getD false := by
  by_cases hi : i < word.length
  · rw [List.getElem?_eq_getElem hi]
    exact testBit_toNat word i hi
  · rw [List.getElem?_eq_none (by omega)]
    apply Nat.testBit_lt_two_pow
    exact (ModularArithmetic.toNat_lt_pow_length word).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega))

def chunkValue {b : ℕ} (x : Chunk b) : ℕ := BinaryArithmetic.toNat (List.ofFn x)

theorem chunkValue_lt {b : ℕ} (x : Chunk b) : chunkValue x < 2 ^ b := by
  simpa [chunkValue] using ModularArithmetic.toNat_lt_pow_length (List.ofFn x)

@[simp] theorem testBit_chunkValue {b : ℕ} (x : Chunk b) (i : Fin b) :
    (chunkValue x).testBit i.val = x i := by
  simpa [chunkValue] using testBit_toNat (List.ofFn x) i.val (by simp)

theorem chunkValue_injective (b : ℕ) : Function.Injective (@chunkValue b) := by
  intro x y h
  funext i
  calc
    x i = (chunkValue x).testBit i.val := (testBit_chunkValue x i).symm
    _ = (chunkValue y).testBit i.val := by rw [h]
    _ = y i := testBit_chunkValue y i

/-- A total low-bit decoder; validity is needed only to re-encode exactly. -/
def decodeChunk (b n : ℕ) : Chunk b := fun i => n.testBit i.val

@[simp] theorem decodeChunk_chunkValue {b : ℕ} (x : Chunk b) :
    decodeChunk b (chunkValue x) = x := by
  funext i
  exact testBit_chunkValue x i

theorem chunkValue_decodeChunk (b n : ℕ) (hn : n < 2 ^ b) :
    chunkValue (decodeChunk b n) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · exact testBit_chunkValue (decodeChunk b n) ⟨i, hi⟩
  · have hpow : 2 ^ b ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
    rw [Nat.testBit_lt_two_pow ((chunkValue_lt (decodeChunk b n)).trans_le hpow),
      Nat.testBit_lt_two_pow (hn.trans_le hpow)]

def chunkEquiv (b : ℕ) : Chunk b ≃ Fin (2 ^ b) where
  toFun x := ⟨chunkValue x, chunkValue_lt x⟩
  invFun n := decodeChunk b n.val
  left_inv := decodeChunk_chunkValue
  right_inv n := Fin.ext (chunkValue_decodeChunk b n.val n.isLt)

def chunkEmbedding {b p : ℕ} (h : 2 ^ b ≤ p) : Chunk b ↪ Fin p where
  toFun x := ⟨chunkValue x, (chunkValue_lt x).trans_le h⟩
  inj' _x _y he := chunkValue_injective b (congrArg Fin.val he)

@[simp] theorem chunkEmbedding_val {b p : ℕ} (h : 2 ^ b ≤ p) (x : Chunk b) :
    (chunkEmbedding h x).val = chunkValue x := rfl

theorem mem_range_chunkEmbedding {b p : ℕ} (h : 2 ^ b ≤ p) (a : Fin p) :
    a ∈ Set.range (chunkEmbedding h) ↔ a.val < 2 ^ b := by
  constructor
  · rintro ⟨x, rfl⟩
    exact chunkValue_lt x
  · intro ha
    exact ⟨decodeChunk b a.val, Fin.ext (chunkValue_decodeChunk b a.val ha)⟩

def chunkZModEmbedding {b p : ℕ} [NeZero p] (h : 2 ^ b ≤ p) : Chunk b ↪ ZMod p where
  toFun x := ZMod.finEquiv p (chunkEmbedding h x)
  inj' _x _y he := (chunkEmbedding h).injective ((ZMod.finEquiv p).injective he)

@[simp] theorem chunkZModEmbedding_val {b p : ℕ} [NeZero p]
    (h : 2 ^ b ≤ p) (x : Chunk b) :
    (chunkZModEmbedding h x).val = chunkValue x :=
  BooleanPacking.finEquiv_val _

theorem mem_range_chunkZModEmbedding {b p : ℕ} [NeZero p]
    (h : 2 ^ b ≤ p) (a : ZMod p) :
    a ∈ Set.range (chunkZModEmbedding h) ↔ a.val < 2 ^ b := by
  constructor
  · rintro ⟨x, rfl⟩
    simpa using chunkValue_lt x
  · intro ha
    refine ⟨decodeChunk b a.val, (ZMod.val_injective p) ?_⟩
    rw [chunkZModEmbedding_val, chunkValue_decodeChunk b a.val ha]

def decodeZMod (b : ℕ) {p : ℕ} (a : ZMod p) : Chunk b := decodeChunk b a.val

@[simp] theorem decodeZMod_encode {b p : ℕ} [NeZero p]
    (h : 2 ^ b ≤ p) (x : Chunk b) : decodeZMod b (chunkZModEmbedding h x) = x := by
  simp [decodeZMod]

theorem encode_decodeZMod {b p : ℕ} [NeZero p]
    (h : 2 ^ b ≤ p) (a : ZMod p) (ha : a.val < 2 ^ b) :
    chunkZModEmbedding h (decodeZMod b a) = a := by
  apply ZMod.val_injective p
  rw [chunkZModEmbedding_val]
  exact chunkValue_decodeChunk b a.val ha

/-- The materializer's actual word lookup equals the matching semantic
chunk decoder, for every available bit. No validity premise is hidden here. -/
theorem word_getElem_eq_decodeZMod {b p : ℕ} (a : ZMod p) (word : List Bool)
    (hword : BinaryArithmetic.toNat word = a.val) (hwidth : b ≤ word.length) (i : Fin b) :
    word[i.val]'(i.isLt.trans_le hwidth) = decodeZMod b a i := by
  rw [getElem_eq_testBit, hword]
  rfl

theorem fixedBits_getElem (b n : ℕ) (i : Fin b) :
    (SubexpLiftRing.fixedBits b n)[i.val]'(by simp) = n.testBit i.val := by
  rw [getElem_eq_testBit, SubexpLiftRing.toNat_fixedBits, Nat.testBit_mod_two_pow]
  simp [i.isLt]

theorem ofFn_decodeChunk (b n : ℕ) :
    List.ofFn (decodeChunk b n) = SubexpLiftRing.fixedBits b n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hib : i < b := by simpa using hi
    simpa [decodeChunk] using (fixedBits_getElem b n ⟨i, hib⟩).symm

private theorem value_append (low high : List Bool) :
    BinaryArithmetic.toNat (low ++ high) = BinaryArithmetic.toNat low + 2 ^ low.length * BinaryArithmetic.toNat high := by
  induction low with
  | nil => simp
  | cons bit low ih =>
    simp only [List.cons_append, toNat_cons, List.length_cons, ih, pow_succ]
    ring

/-- The old recursive equivalence reads its first coordinate as the most
significant bit. This exact formula makes the convention difference explicit. -/
theorem msb_value (b : ℕ) : ∀ x : Chunk b,
    (BooleanPacking.chunkEquiv b x).val = BinaryArithmetic.toNat (List.ofFn (fun i => x i.rev)) := by
  induction b with
  | zero =>
    intro x
    have h := (BooleanPacking.chunkEquiv 0 x).isLt
    simp only [pow_zero] at h
    simp
  | succ b ih =>
    intro x
    have hb : (finTwoEquiv.symm (x 0)).val = bitVal (x 0) := by
      cases x 0 <;> rfl
    have hlist : List.ofFn (fun i : Fin (b + 1) => x i.rev) =
        List.ofFn (fun i : Fin b => x i.rev.succ) ++ [x 0] := by
      simpa only [Fin.rev_castSucc, Fin.rev_last, List.concat_eq_append] using
        List.ofFn_succ' (fun i : Fin (b + 1) => x i.rev)
    change (BooleanPacking.chunkEquiv b (fun i => x i.succ)).val +
      2 ^ b * (finTwoEquiv.symm (x 0)).val = _
    rw [ih, hb, hlist, value_append, List.length_ofFn]
    simp

/-- Reversal is at the actual b-bit chunk, including a short final chunk. -/
theorem chunkEmbedding_eq_msb_rev {b p : ℕ} (h : 2 ^ b ≤ p) (x : Chunk b) :
    chunkEmbedding h x = BooleanPacking.chunkEmbedding h (fun i => x i.rev) := by
  apply Fin.ext
  change chunkValue x = (BooleanPacking.chunkEquiv b (fun i => x i.rev)).val
  rw [msb_value]
  simp [chunkValue]

theorem chunkZModEmbedding_eq_msb_rev {b p : ℕ} [NeZero p]
    (h : 2 ^ b ≤ p) (x : Chunk b) :
    chunkZModEmbedding h x = BooleanPacking.chunkZModEmbedding h (fun i => x i.rev) := by
  change ZMod.finEquiv p (chunkEmbedding h x) =
    ZMod.finEquiv p (BooleanPacking.chunkEmbedding h (fun i => x i.rev))
  exact congrArg (ZMod.finEquiv p) (chunkEmbedding_eq_msb_rev h x)

end SubexponentialSAT.BooleanPackingLE

end OAI.Algorithms
