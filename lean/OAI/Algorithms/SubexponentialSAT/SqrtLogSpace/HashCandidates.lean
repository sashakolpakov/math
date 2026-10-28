import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayloadSelect
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration
import Mathlib.Data.List.SplitLengths

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

/-- Positive chunk width, computed from the ternary coordinate alphabet. -/
def digitWidth (m : ℕ) : ℕ := DyadicWidth.width (3 * m)

/-- Number of retained payload bits, rather than the number of candidates. -/
def payloadWidth (m depth : ℕ) : ℕ := depth * digitWidth m

/-- Proof-level accessor for the word present at a binary odometer rank. -/
def payload (m depth : ℕ) (i : Fin (2 ^ payloadWidth m depth)) : List Bool :=
  (ExecCNFTupleEnumeration.fixedBits (payloadWidth m depth) i.val).reverse

@[simp] theorem payload_length (m depth : ℕ) (i : Fin (2 ^ payloadWidth m depth)) :
    (payload m depth i).length = payloadWidth m depth := by
  simp [payload]

@[simp] theorem payload_value (m depth : ℕ) (i : Fin (2 ^ payloadWidth m depth)) :
    CounterPrograms.value (payload m depth i).reverse = i.val := by
  simpa [payload] using ExecCNFTupleEnumeration.fixedBits_value _ _ i.isLt

theorem payload_covers_word {m depth : ℕ} (bits : List Bool)
    (hb : bits.length = payloadWidth m depth) :
    ∃ i, payload m depth i = bits := by
  have hv : CounterPrograms.value bits.reverse < 2 ^ payloadWidth m depth := by
    simpa only [List.length_reverse, hb] using ExecCNFTupleOdometer.value_lt_power_length bits.reverse
  refine ⟨⟨CounterPrograms.value bits.reverse, hv⟩, ?_⟩
  apply List.reverse_injective
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · simp [hb]
  · simp

theorem digitWidth_sufficient (m : ℕ) : 3 * m ≤ 2 ^ digitWidth m :=
  (DyadicWidth.lt_two_pow_width _).le

theorem encode_length {m depth : ℕ} (h : Candidate m depth) :
    (HashFamilyPayload.encode (digitWidth m) h).length = payloadWidth m depth :=
  HashFamilyPayload.generated_payload_width _ _ _ _
    (HashFamilyPayload.encode_mem _ h)

/-- All binary trials, including duplicate decoded rows, fit a fixed square
of the original explicit ternary family count. -/
theorem candidate_count_le_square {m : ℕ} (hm : 0 < m) (depth : ℕ) :
    2 ^ payloadWidth m depth ≤ ((3 * m) ^ depth) ^ 2 := by
  have hbase : 2 ^ digitWidth m ≤ (3 * m) ^ 2 := by
    have h := DyadicWidth.two_pow_width_le (3 * m)
    dsimp [digitWidth]
    nlinarith
  calc
    2 ^ payloadWidth m depth = (2 ^ digitWidth m) ^ depth := by
      rw [payloadWidth, Nat.mul_comm, pow_mul]
    _ ≤ ((3 * m) ^ 2) ^ depth := Nat.pow_le_pow_left hbase depth
    _ = ((3 * m) ^ depth) ^ 2 := by simp [← pow_mul, Nat.mul_comm]

theorem payloadWidth_le (m depth : ℕ) : payloadWidth m depth ≤ depth * (3 * m + 1) :=
  Nat.mul_le_mul_left depth (DyadicWidth.width_le_succ (3 * m))

/-- Even the value of the exponential visit count needs only one more bit
than the retained candidate word. The iterator uses overflow, not this count. -/
theorem visit_count_binary_width (m depth : ℕ) :
    Nat.size (2 ^ payloadWidth m depth) = payloadWidth m depth + 1 :=
  Nat.size_pow

@[simp] theorem zero_depth_payload (m : ℕ) (i : Fin (2 ^ payloadWidth m 0)) :
    payload m 0 i = [] := by
  simp [payload, payloadWidth, ExecCNFTupleEnumeration.fixedBits]


/-- A proof-level partition of the one retained raw payload. Its length is
only the number of hash slots, never the number of candidates. -/
def chunks (m depth : ℕ) (raw : List Bool) : List (List Bool) :=
  (List.replicate depth (digitWidth m)).splitLengths raw.reverse

@[simp] theorem chunks_length (m depth : ℕ) (raw : List Bool) :
    (chunks m depth raw).length = depth := by simp [chunks]

theorem chunks_shape {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    (chunks m depth raw).map List.length = List.replicate depth (digitWidth m) := by
  apply List.map_splitLengths_length
  simp [hraw, payloadWidth]

theorem chunks_width {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    ∀ word ∈ chunks m depth raw, word.length = digitWidth m := by
  intro word hw
  have hmem : word.length ∈ (chunks m depth raw).map List.length :=
    List.mem_map.mpr ⟨word, hw, rfl⟩
  rw [chunks_shape hraw] at hmem
  exact (List.mem_replicate.mp hmem).2

theorem chunks_flatten {m depth : ℕ} {raw : List Bool}
    (hraw : raw.length = payloadWidth m depth) :
    (chunks m depth raw).flatten = raw.reverse := by
  apply List.flatten_splitLengths
  simp [hraw, payloadWidth]

/-- Canonicalization modulo the indexed ternary alphabet is performed before
lifting coefficients into the existing characteristic-3-power ring. -/
def normalize (m depth : ℕ) (raw : List Bool) : List Bool :=
  ((chunks m depth raw).map fun word =>
    SubexpLiftRing.fixedBits (digitWidth m) (BinaryArithmetic.toNat word % (3 * m))).flatten.reverse

@[simp] theorem normalize_length (m depth : ℕ) (raw : List Bool) :
    (normalize m depth raw).length = payloadWidth m depth := by
  simp [normalize, List.length_flatten, List.map_map, payloadWidth,
    Function.comp_def]

/-- The actual normalizer emits the original valid candidate encoding family,
so the old native row assembler can be reused with its original hypotheses. -/
theorem normalize_mem {m : ℕ} (hm : 0 < m) (depth : ℕ) (raw : List Bool) :
    normalize m depth raw ∈
      HashSelectProgram.generatedPayloads (HashFamilyPayload.alphabet m (digitWidth m)) depth := by
  let words := (chunks m depth raw).map fun word =>
    SubexpLiftRing.fixedBits (digitWidth m) (BinaryArithmetic.toNat word % (3 * m))
  apply List.mem_map.mpr
  refine ⟨words.flatten, ?_, rfl⟩
  have hwords : ∀ word ∈ words, word ∈ HashFamilyPayload.alphabet m (digitWidth m) := by
    intro word hw
    obtain ⟨chunk, _, rfl⟩ := List.mem_map.mp hw
    exact List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩
  have h := HashFamilyPayload.powerRows_contains
    (HashFamilyPayload.alphabet m (digitWidth m)) words [[]] [] (by simp) hwords
  simpa [words] using h

theorem normalize_valid {m depth : ℕ} (raw : List Bool)
    (hr : raw ∈ HashSelectProgram.generatedPayloads
      (HashFamilyPayload.alphabet m (digitWidth m)) depth) : normalize m depth raw = raw := by
  have hraw : raw.length = payloadWidth m depth :=
    HashFamilyPayload.generated_payload_width _ _ _ _ hr
  have hread : HashFamilyPayload.readChunks (digitWidth m) depth raw.reverse =
      (chunks m depth raw).map BinaryArithmetic.toNat := by
    have h := HashFamilyPayload.readChunks_uniform (digitWidth m) (chunks m depth raw)
      (chunks_width hraw)
    simpa [chunks_flatten hraw] using h
  have hmap : (chunks m depth raw).map (fun word =>
      SubexpLiftRing.fixedBits (digitWidth m) (BinaryArithmetic.toNat word % (3 * m))) =
        chunks m depth raw := by
    conv_rhs => rw [← List.map_id (chunks m depth raw)]
    apply List.map_congr_left
    intro word hw
    have hmem : BinaryArithmetic.toNat word ∈
        HashFamilyPayload.readChunks (digitWidth m) depth raw.reverse := by
      rw [hread]
      exact List.mem_map.mpr ⟨word, hw, rfl⟩
    have hv := HashFamilyPayload.generated_chunks_valid (digitWidth_sufficient m) raw hr _ hmem
    apply ExecCNFTupleEnumeration.word_eq_of_length_value
    · simp [chunks_width hraw word hw]
    · rw [CounterPrograms.value_eq_toNat, CounterPrograms.value_eq_toNat,
        Nat.mod_eq_of_lt hv, SubexpLiftRing.toNat_fixedBits_of_lt _ _
          (hv.trans_le (digitWidth_sufficient m))]
      rfl
  simp [normalize, hmap, chunks_flatten hraw]

theorem normalized_covers_candidate {m depth : ℕ}
    (h : Candidate m depth) :
    ∃ i, normalize m depth (payload m depth i) = HashFamilyPayload.encode (digitWidth m) h := by
  obtain ⟨i, hi⟩ := payload_covers_word
    (HashFamilyPayload.encode (digitWidth m) h) (encode_length h)
  refine ⟨i, ?_⟩
  rw [hi]
  exact normalize_valid _ (HashFamilyPayload.encode_mem _ h)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
