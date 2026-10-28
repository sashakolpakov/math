import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSelectedFamilyProgram

namespace OAI.Algorithms

/-! Output-size bounds for the actual encoded indexed-family builder. -/

namespace SubexponentialSAT.ExecSelectedFamilySize

open ExecSelectedFamilyProgram

theorem member_encoded_length_le {α : Type*} (enc : α → List Bool)
    (xs : List α) (x : α) (hx : x ∈ xs) :
    (enc x).length ≤ (Encoding.encodeList enc xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst y
        rw [Encoding.length_encodeList_cons]
        omega
      · have ht := ih h
        rw [Encoding.length_encodeList_cons]
        omega

theorem gather_encoded_length_le {α : Type*} (enc : α → List Bool)
    (xs : List α) (words : List (List Bool)) :
    (Encoding.encodeList enc
      (words.filterMap (fun bits => xs[CounterPrograms.value bits]?)).reverse).length ≤
      2 * ((Encoding.encodeList enc xs).length + 1) * ((encode words).length + 1) := by
  have hK : ∀ x ∈ (words.filterMap (fun bits => xs[CounterPrograms.value bits]?)).reverse,
      (enc x).length ≤ (Encoding.encodeList enc xs).length := by
    intro x hx
    have hm := List.mem_reverse.mp hx
    obtain ⟨bits, _, hbits⟩ := List.mem_filterMap.mp hm
    exact member_encoded_length_le enc xs x (List.mem_of_getElem? hbits)
  have hb := Encoding.length_encodeList_upper enc
    (words.filterMap (fun bits => xs[CounterPrograms.value bits]?)).reverse
    (Encoding.encodeList enc xs).length hK
  rw [List.length_reverse] at hb
  have hs := List.length_filterMap_le (fun bits => xs[CounterPrograms.value bits]?) words
  have hw := Encoding.length_encodeList_lower (id : List Bool → List Bool) words
  change words.length + 1 ≤ (encode words).length at hw
  have hlen : (words.filterMap (fun bits => xs[CounterPrograms.value bits]?)).length ≤
      (encode words).length := by omega
  have hmul := Nat.mul_le_mul_left (2 * (Encoding.encodeList enc xs).length + 2) hlen
  nlinarith

/-- The exact bound needed before scanning the gathered CNF for its first
clause and core. It also holds when the index tuple has invalid entries. -/
theorem clause_family_output_length_le (formula : List (List (List Bool)))
    (words : List (List Bool)) :
    (Encoding.encodeList encode (selectedClauses formula words).reverse).length ≤
      2 * ((Encoding.encodeList encode formula).length + 1) * ((encode words).length + 1) :=
  gather_encoded_length_le encode formula words

end SubexponentialSAT.ExecSelectedFamilySize

end OAI.Algorithms
