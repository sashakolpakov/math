import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily
open SubexponentialSAT.Subexp TupleProgram
open SubexponentialSAT.SubexpLiftRing (fixedBits)
open SubexponentialSAT.BinaryArithmetic (toNat)

theorem powerRows_decompose (alphabet rows : List (List Bool)) (depth : ℕ)
    (bits : List Bool) (hbits : bits ∈ powerRows alphabet depth rows) :
    ∃ front ∈ rows, ∃ words : List (List Bool),
      words.length = depth ∧ (∀ word ∈ words, word ∈ alphabet) ∧
      bits = front ++ words.flatten := by
  induction depth generalizing rows with
  | zero => exact ⟨bits, hbits, [], rfl, by simp, by simp⟩
  | succ depth ih =>
      obtain ⟨mid, hmid, words, hlen, hw, heq⟩ :=
        ih (cartesianOutput rows alphabet) hbits
      simp only [cartesianOutput, List.mem_reverse, List.mem_flatMap] at hmid
      obtain ⟨front, hp, hmid⟩ := hmid
      obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hmid
      refine ⟨front, hp, word :: words, by simp [hlen], ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hword
        · exact hw a ha
      · simpa [List.flatten_cons, List.append_assoc] using heq

theorem readChunks_uniform (width : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width) :
    readChunks width words.length words.flatten = words.map BinaryArithmetic.toNat := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      have hword := hw word (by simp)
      have hwords : ∀ a ∈ words, a.length = width := by
        intro a ha
        exact hw a (by simp [ha])
      have ht (tail : List Bool) : (word ++ tail).take width = word := by
        exact List.take_left' hword
      have hd (tail : List Bool) : (word ++ tail).drop width = tail := by
        exact List.drop_left' hword
      simp only [List.length_cons, List.flatten_cons, List.map_cons, readChunks, ht, hd]
      rw [ih hwords]

@[simp] theorem readChunks_length (width depth : ℕ) (bits : List Bool) :
    (readChunks width depth bits).length = depth := by
  induction depth generalizing bits with
  | zero => rfl
  | succ depth ih => simp [readChunks, ih]

theorem generated_chunks_valid {m width depth : ℕ}
    (hw : 3 * m ≤ 2 ^ width) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    ∀ v ∈ readChunks width depth payload.reverse, v < 3 * m := by
  obtain ⟨bits, hbits, rfl⟩ := List.mem_map.mp hp
  obtain ⟨front, hfront, words, hlen, hwords, heq⟩ :=
    powerRows_decompose (alphabet m width) [[]] depth bits hbits
  have hpref : front = [] := by simpa using hfront
  subst front
  simp only [List.nil_append] at heq
  subst bits
  rw [List.reverse_reverse, ← hlen, readChunks_uniform width words
    (fun a ha => alphabet_width m width a (hwords a ha))]
  intro v hv
  obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (hwords word hword)
  have hi' := List.mem_range.mp hi
  rw [SubexpLiftRing.toNat_fixedBits_of_lt _ _ (hi'.trans_le hw)]
  exact hi'

theorem generated_payload_width (m width depth : ℕ) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    payload.length = depth * width :=
  HashSelectProgram.generatedPayloads_width _ _ _ (alphabet_width m width) _ hp

@[simp] theorem generated_count (m width depth : ℕ) :
    (HashSelectProgram.generatedPayloads (alphabet m width) depth).length = (3 * m) ^ depth := by
  simp

theorem generated_nonempty {m : ℕ} (hm : 0 < m) (width depth : ℕ) :
    HashSelectProgram.generatedPayloads (alphabet m width) depth ≠ [] := by
  intro he
  have hpos : 0 < (3 * m) ^ depth := Nat.pow_pos (by omega)
  have hlen := generated_count m width depth
  rw [he] at hlen
  simp only [List.length_nil] at hlen
  omega

def canonicalWidth (m : ℕ) : ℕ := Nat.size (3 * m)

theorem canonicalWidth_sufficient (m : ℕ) : 3 * m < 2 ^ canonicalWidth m :=
  Nat.lt_size_self _

theorem digit_coordinate_value {m : ℕ} (a : Fin (3 * m)) :
    ((digitEquiv m).symm a).1.val = a.val % m := rfl

theorem digit_coefficient_value {m : ℕ} (a : Fin (3 * m)) :
    ((digitEquiv m).symm a).2.val = a.val / m := rfl

/-- The native decoder may use ordinary quotient and remainder on every
generated chunk: the auxiliary modulo `3*m` in the total decoder disappears. -/
theorem generated_decode_values {m width depth : ℕ} (hm : 0 < m)
    (hw : 3 * m ≤ 2 ^ width) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth)
    (j : Fin depth) :
    let v := (readChunks width depth payload.reverse).getD j.val 0
    ((decode m depth width hm payload).1 j).val = v % m ∧
      ((decode m depth width hm payload).2 j).val = v / m := by
  dsimp only
  have hj : j.val < (readChunks width depth payload.reverse).length := by simp
  have hmem : (readChunks width depth payload.reverse).getD j.val 0 ∈
      readChunks width depth payload.reverse := by
    rw [List.getD_eq_getElem _ _ hj]
    exact List.get_mem _ ⟨j.val, hj⟩
  have hv := generated_chunks_valid hw payload hp _ hmem
  change
    (((digitEquiv m).symm
      ⟨(readChunks width depth payload.reverse).getD j.val 0 % (3 * m), _⟩).1).val = _ ∧
    (((digitEquiv m).symm
      ⟨(readChunks width depth payload.reverse).getD j.val 0 % (3 * m), _⟩).2).val = _
  simp only [digit_coordinate_value, digit_coefficient_value ]
  rw [Nat.mod_eq_of_lt hv]
  exact ⟨rfl, rfl⟩

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
