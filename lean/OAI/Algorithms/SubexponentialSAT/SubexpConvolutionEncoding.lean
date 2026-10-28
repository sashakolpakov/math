import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.TruncatedConvolution

namespace OAI.Algorithms

/-! The encoded-array decomposition used by the actual convolution
product-and-update command. No scalar algebra or execution cost is assumed. -/

namespace SubexponentialSAT.SubexpConvolutionEncoding

theorem modify_split {C : Type*} (acc : List C) (i : ℕ) (hi : i < acc.length) :
    ∃ (earlier : List C) (c : C) (rest : List C),
      earlier.length = i ∧ acc = earlier ++ c :: rest ∧
      ∀ f : C → C, acc.modify i f = earlier ++ f c :: rest := by
  induction acc generalizing i with
  | nil => simp at hi
  | cons a acc ih =>
      cases i with
      | zero => exact ⟨[], a, acc, rfl, rfl, fun _ => rfl⟩
      | succ i =>
          obtain ⟨earlier, c, rest, hlen, heq, hmod⟩ := ih i (by simpa using hi)
          refine ⟨a :: earlier, c, rest, ?_, ?_, ?_⟩
          · simp [hlen]
          · simp [heq]
          · intro f
            simp only [List.modify_succ_cons, hmod, List.cons_append]

def encodeArray {C : Type*} (encode : C → List Bool) (acc : List C) : List Bool :=
  (acc.map encode).flatten

theorem encode_addProduct_split {C : Type*}
    (encode : C → List Bool) (width : ℕ) (hwidth : ∀ c, (encode c).length = width)
    (add mul : C → C → C) (acc : List C) (i : ℕ) (a b : C)
    (hi : i < acc.length) :
    ∃ (earlier : List (List Bool)) (c : C) (rest : List Bool),
      earlier.length = i ∧
      (∀ bits ∈ earlier, bits.length = width) ∧
      encodeArray encode acc = earlier.flatten ++ (encode c ++ rest) ∧
      encodeArray encode (TruncatedConvolution.addProduct add mul i a b acc) =
        earlier.flatten ++ (encode (add (mul a b) c) ++ rest) := by
  obtain ⟨earlier, c, rest, hlen, heq, hmod⟩ := modify_split acc i hi
  refine ⟨earlier.map encode, c, encodeArray encode rest, ?_, ?_, ?_, ?_⟩
  · simpa using hlen
  · intro bits hbits
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hbits
    exact hwidth x
  · simp [encodeArray, heq]
  · rw [TruncatedConvolution.addProduct, hmod]
    simp [encodeArray]

end SubexponentialSAT.SubexpConvolutionEncoding

end OAI.Algorithms
