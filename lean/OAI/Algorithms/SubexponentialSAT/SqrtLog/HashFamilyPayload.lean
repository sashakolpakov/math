import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyDigits
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramGenerate
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

namespace OAI.Algorithms

/-! The actual tuple-generator bit alphabet and its reverse-aware semantic
decoder. The alphabet matches `SubexpAlphabetProgram.command_eval`. -/

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily
open SubexponentialSAT.Subexp TupleProgram
open SubexponentialSAT.SubexpLiftRing (fixedBits)
open SubexponentialSAT.BinaryArithmetic (toNat)

def alphabet (m width : ℕ) : List (List Bool) :=
  (List.range (3 * m)).map (fixedBits width)

def readChunks (width : ℕ) : ℕ → List Bool → List ℕ
  | 0, _ => []
  | depth + 1, bits =>
      BinaryArithmetic.toNat (bits.take width) :: readChunks width depth (bits.drop width)

def encodeDigits {m depth : ℕ} (width : ℕ) (a : Fin depth → Fin (3 * m)) : List Bool :=
  ((List.ofFn fun j => fixedBits width (a j).val).flatten).reverse

def encode {m depth : ℕ} (width : ℕ) (h : Candidate m depth) : List Bool :=
  encodeDigits width (candidateDigitsEquiv m depth h)

def decode (m depth width : ℕ) (hm : 0 < m) (payload : List Bool) : Candidate m depth :=
  decodeDigits fun j =>
    ⟨(readChunks width depth payload.reverse).getD j.val 0 % (3 * m),
      Nat.mod_lt _ (by omega)⟩

/-- A total row decoder; the zero-dimensional case has only the zero row. -/
def decodeRow (m depth width : ℕ) (payload : List Bool) : Fin m → ZMod 3 :=
  if hm : 0 < m then row (decode m depth width hm payload) else fun _ => 0

@[simp] theorem alphabet_length (m width : ℕ) : (alphabet m width).length = 3 * m := by
  simp [alphabet]

theorem alphabet_width (m width : ℕ) :
    ∀ a ∈ alphabet m width, a.length = width := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  simp

theorem readChunks_encode (width : ℕ) (xs : List ℕ)
    (hx : ∀ i ∈ xs, i < 2 ^ width) :
    readChunks width xs.length ((xs.map (fixedBits width)).flatten) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hhead := hx x (by simp)
      have htail : ∀ i ∈ xs, i < 2 ^ width := by
        intro i hi
        exact hx i (by simp [hi])
      have ht (tail : List Bool) : (fixedBits width x ++ tail).take width = fixedBits width x := by
        simp
      have hd (tail : List Bool) : (fixedBits width x ++ tail).drop width = tail := by
        simp
      simp only [List.length_cons, List.map_cons, List.flatten_cons, readChunks, ht, hd]
      rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ hhead, ih htail]

theorem decode_encodeDigits {m depth : ℕ} (hm : 0 < m) (width : ℕ)
    (hw : 3 * m ≤ 2 ^ width) (a : Fin depth → Fin (3 * m)) :
    decode m depth width hm (encodeDigits width a) = decodeDigits a := by
  apply congrArg decodeDigits
  funext j
  apply Fin.ext
  have hx : ∀ i ∈ List.ofFn (fun j => (a j).val), i < 2 ^ width := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact (a j).isLt.trans_le hw
  have hc := readChunks_encode width (List.ofFn fun j => (a j).val) hx
  simp only [List.length_ofFn, List.map_ofFn, Function.comp_def] at hc
  simp only [ encodeDigits, List.reverse_reverse]
  rw [hc]
  simp [Nat.mod_eq_of_lt (a j).isLt]

theorem decode_encode {m depth : ℕ} (hm : 0 < m) (width : ℕ)
    (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    decode m depth width hm (encode width h) = h := by
  rw [encode, decode_encodeDigits hm width hw]
  exact (candidateDigitsEquiv m depth).symm_apply_apply h

theorem decodeRow_encode {m depth : ℕ} (hm : 0 < m) (width : ℕ)
    (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    decodeRow m depth width (encode width h) = row h := by
  simp [decodeRow, hm, decode_encode hm width hw]

theorem decodeRow_support (m depth width : ℕ) (payload : List Bool) :
    supportCard (decodeRow m depth width payload) ≤ depth := by
  unfold decodeRow
  split_ifs with hm
  · exact row_support_le _
  · simp [supportCard]

theorem cartesian_mem {alphabet rows : List (List Bool)} {front word : List Bool}
    (hp : front ∈ rows) (hw : word ∈ alphabet) :
    front ++ word ∈ cartesianOutput rows alphabet := by
  simp only [cartesianOutput, List.mem_reverse, List.mem_flatMap]
  exact ⟨front, hp, List.mem_map.mpr ⟨word, hw, rfl⟩⟩

/-- Internal reversals of the generator's list order do not affect coverage. -/
theorem powerRows_contains (alphabet words rows : List (List Bool)) (front : List Bool)
    (hp : front ∈ rows) (hw : ∀ a ∈ words, a ∈ alphabet) :
    front ++ words.flatten ∈ powerRows alphabet words.length rows := by
  induction words generalizing rows front with
  | nil => simpa [powerRows] using hp
  | cons word words ih =>
      have hword : word ∈ alphabet := hw word (by simp)
      have hwords : ∀ a ∈ words, a ∈ alphabet := by
        intro a ha
        exact hw a (by simp [ha])
      have h := ih (cartesianOutput rows alphabet) (front ++ word)
        (cartesian_mem hp hword) hwords
      simpa [powerRows, List.flatten_cons, List.append_assoc] using h

theorem encodeDigits_mem {m depth : ℕ} (width : ℕ) (a : Fin depth → Fin (3 * m)) :
    encodeDigits width a ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth := by
  apply List.mem_map.mpr
  refine ⟨(List.ofFn fun j => fixedBits width (a j).val).flatten, ?_, rfl⟩
  have h := powerRows_contains (alphabet m width)
    (List.ofFn fun j => fixedBits width (a j).val) [[]] [] (by simp) ?_
  · simpa using h
  · intro word hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    exact List.mem_map.mpr ⟨(a j).val, List.mem_range.mpr (a j).isLt, rfl⟩

theorem encode_mem {m depth : ℕ} (width : ℕ) (h : Candidate m depth) :
    encode width h ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth :=
  encodeDigits_mem width _

/-- Exact list coverage consumed by `HashSelect.listRun`: the generator emits
a payload for every indexed candidate, regardless of its internal order. -/
theorem generated_coverage {m depth : ℕ} (hm : 0 < m) (width : ℕ)
    (hw : 3 * m ≤ 2 ^ width) (h : Candidate m depth) :
    ∃ payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth,
      decodeRow m depth width payload = row h :=
  ⟨encode width h, encode_mem width h, decodeRow_encode hm width hw h⟩

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
