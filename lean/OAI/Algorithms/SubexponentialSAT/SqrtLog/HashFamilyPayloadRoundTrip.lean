import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayloadValid
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily
open SubexponentialSAT.Subexp TupleProgram
open SubexponentialSAT.SubexpLiftRing (fixedBits)
open SubexponentialSAT.BinaryArithmetic (toNat)

theorem ofFn_getD_values (values : List ℕ) (depth : ℕ) (hlen : values.length = depth) :
    List.ofFn (fun j : Fin depth => values.getD j.val 0) = values := by
  subst depth
  have hf : (fun j : Fin values.length => values.getD j.val 0) = values.get := by
    funext j
    exact List.getD_eq_getElem values 0 j.isLt
  rw [hf, List.ofFn_get]

theorem fixedBits_toNat (word : List Bool) :
    fixedBits word.length (BinaryArithmetic.toNat word) = word := by
  simpa only [CounterPrograms.value_eq_toNat] using
    (SubexpAlphabetProgram.canonical_word word).symm

theorem generated_reconstruct {m width depth : ℕ} (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    (((readChunks width depth payload.reverse).map (fixedBits width)).flatten).reverse =
      payload := by
  obtain ⟨bits, hbits, rfl⟩ := List.mem_map.mp hp
  obtain ⟨front, hfront, words, hlen, hwords, heq⟩ :=
    powerRows_decompose (alphabet m width) [[]] depth bits hbits
  have hf : front = [] := by simpa using hfront
  subst front
  simp only [List.nil_append] at heq
  subst bits
  rw [List.reverse_reverse, ← hlen, readChunks_uniform width words
    (fun a ha => alphabet_width m width a (hwords a ha))]
  have hm : (words.map BinaryArithmetic.toNat).map (fixedBits width) = words := by
    rw [List.map_map]
    calc
      words.map (fixedBits width ∘ BinaryArithmetic.toNat) = words.map id := by
        apply List.map_congr_left
        intro word hword
        have hw := alphabet_width m width word (hwords word hword)
        simpa only [Function.comp_apply, id_eq, hw] using fixedBits_toNat word
      _ = words := List.map_id words
  rw [hm]

/-- Every actual generated record has exactly the canonical encoding of its
decoded candidate. This is stronger than equality of the induced row. -/
theorem encode_decode_generated {m depth width : ℕ} (hm : 0 < m)
    (hw : 3 * m ≤ 2 ^ width) (payload : List Bool)
    (hp : payload ∈ HashSelectProgram.generatedPayloads (alphabet m width) depth) :
    encode width (decode m depth width hm payload) = payload := by
  let values := readChunks width depth payload.reverse
  have hlen : values.length = depth := readChunks_length width depth payload.reverse
  have hvalid : ∀ v ∈ values, v < 3 * m := generated_chunks_valid hw payload hp
  have hget (j : Fin depth) : values.getD j.val 0 < 3 * m := by
    have hj : j.val < values.length := by simpa only [hlen] using j.isLt
    apply hvalid
    rw [List.getD_eq_getElem values 0 hj]
    exact List.get_mem values ⟨j.val, hj⟩
  have hlist : List.ofFn (fun j : Fin depth => values.getD j.val 0 % (3 * m)) = values := by
    have hf : (fun j : Fin depth => values.getD j.val 0 % (3 * m)) =
        (fun j : Fin depth => values.getD j.val 0) := by
      funext j
      exact Nat.mod_eq_of_lt (hget j)
    rw [hf]
    exact ofFn_getD_values values depth hlen
  change encodeDigits width ((candidateDigitsEquiv m depth)
    ((candidateDigitsEquiv m depth).symm (fun j =>
      ⟨values.getD j.val 0 % (3 * m), Nat.mod_lt _ (by omega)⟩))) = payload
  rw [Equiv.apply_symm_apply]
  unfold encodeDigits
  have hmap :
      List.ofFn (fun j : Fin depth => fixedBits width (values.getD j.val 0 % (3 * m))) =
        values.map (fixedBits width) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map (fixedBits width)) hlist
  change (List.ofFn (fun j : Fin depth =>
    fixedBits width (values.getD j.val 0 % (3 * m)))).flatten.reverse = payload
  rw [hmap]
  exact generated_reconstruct payload hp

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
