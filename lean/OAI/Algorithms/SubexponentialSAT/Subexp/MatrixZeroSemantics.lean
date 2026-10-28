import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockZeroProgram

namespace OAI.Algorithms

/-! Canonical-field interpretation of the actual framed zero scanner. -/

namespace SubexponentialSAT.Subexp.MatrixZeroSemantics

open BinaryArithmetic

theorem frames_eq_words (xs : List (List Bool)) :
    BlockZeroProgram.frames xs = MatrixProgramSupport.words xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [BlockZeroProgram.frames, MatrixProgramSupport.words, ← ih]

theorem bits_zero_iff (bits : List Bool) : bits.all (! ·) = true ↔ BinaryArithmetic.toNat bits = 0 := by
  induction bits with
  | nil => simp [BinaryArithmetic.toNat]
  | cons b bits ih =>
    cases b <;> simp [BinaryArithmetic.toNat, bitVal, ih]

theorem isZero_iff (xs : List (List Bool)) :
    BlockZeroProgram.isZero xs = true ↔ ∀ bits ∈ xs, BinaryArithmetic.toNat bits = 0 := by
  rw [BlockZeroProgram.isZero, List.all_eq_true]
  constructor
  · intro h bits hb
    exact (bits_zero_iff bits).mp (h bits hb)
  · intro h bits hb
    exact (bits_zero_iff bits).mpr (h bits hb)

theorem canonical_zero_iff (p : ℕ) (bits : List Bool) (hc : BinaryArithmetic.toNat bits < p) :
    BinaryArithmetic.toNat bits = 0 ↔ (BinaryArithmetic.toNat bits : ZMod p) = 0 := by
  rw [← ZMod.val_eq_zero, ZMod.val_natCast_of_lt hc]

theorem canonical_isZero_iff (p : ℕ) (xs : List (List Bool))
    (hc : ∀ bits ∈ xs, BinaryArithmetic.toNat bits < p) :
    BlockZeroProgram.isZero xs = true ↔ ∀ bits ∈ xs, (BinaryArithmetic.toNat bits : ZMod p) = 0 := by
  rw [isZero_iff]
  constructor
  · intro h bits hb
    exact (canonical_zero_iff p bits (hc bits hb)).mp (h bits hb)
  · intro h bits hb
    exact (canonical_zero_iff p bits (hc bits hb)).mpr (h bits hb)

theorem zero_encoded_vector_iff (p : ℕ) [Fact p.Prime] {N : ℕ} (x : Fin N → ZMod p) :
    BlockZeroProgram.isZero (List.ofFn fun i => MatrixWordEncoding.word p (x i)) = true ↔ x = 0 := by
  have hc : ∀ bits ∈ List.ofFn (fun i => MatrixWordEncoding.word p (x i)), BinaryArithmetic.toNat bits < p := by
    intro bits hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact MatrixWordEncoding.word_canonical p (x i)
  rw [canonical_isZero_iff p _ hc, List.forall_mem_ofFn_iff]
  simp only [MatrixWordEncoding.word_field_value]
  constructor
  · intro h
    exact funext h
  · intro h i
    rw [h]
    rfl

theorem zero_encoded_vector (p : ℕ) [Fact p.Prime] {N : ℕ} (x : Fin N → ZMod p) :
    BlockZeroProgram.isZero (List.ofFn fun i => MatrixWordEncoding.word p (x i)) = decide (x = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [zero_encoded_vector_iff, decide_eq_true_eq]

theorem zero_decoded_vector_iff (p : ℕ) {N : ℕ} (x : Fin N → ZMod p)
    (xs : List (List Bool)) (hc : ∀ bits ∈ xs, BinaryArithmetic.toNat bits < p)
    (hv : xs.map (fun bits => (BinaryArithmetic.toNat bits : ZMod p)) = List.ofFn x) :
    BlockZeroProgram.isZero xs = true ↔ x = 0 := by
  rw [canonical_isZero_iff p xs hc]
  constructor
  · intro h
    funext i
    have hi : x i ∈ xs.map (fun bits => (BinaryArithmetic.toNat bits : ZMod p)) := by
      rw [hv]
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    obtain ⟨bits, hb, he⟩ := List.mem_map.mp hi
    exact he.symm.trans (h bits hb)
  · intro h bits hb
    have hi : (BinaryArithmetic.toNat bits : ZMod p) ∈ List.ofFn x := by
      rw [← hv]
      exact List.mem_map.mpr ⟨bits, hb, rfl⟩
    obtain ⟨i, he⟩ := List.mem_ofFn.mp hi
    rw [← he, h]
    rfl

end SubexponentialSAT.Subexp.MatrixZeroSemantics

end OAI.Algorithms
