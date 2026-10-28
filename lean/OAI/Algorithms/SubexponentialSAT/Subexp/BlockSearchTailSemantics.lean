import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixZeroSemantics

namespace OAI.Algorithms

/-! The concrete tail slice used by the block coefficient zero test. -/

namespace SubexponentialSAT.Subexp.BlockSearchTailSemantics

open BlockSearchEncoding

theorem ofFn_split {K : Type*} {N : ℕ} (d : Fin (N + 1)) (x : Fin N → K) :
    List.ofFn x = List.ofFn (headCoefficients d x) ++ List.ofFn (tailCoefficients d x) := by
  have hN : d.val + (N - d.val) = N := by have := d.isLt; omega
  rw [List.ofFn_congr hN.symm x, List.ofFn_add]
  rfl

theorem drop_ofFn_eq_tail {K : Type*} {N : ℕ} (d : Fin (N + 1)) (x : Fin N → K) :
    (List.ofFn x).drop d.val = List.ofFn (tailCoefficients d x) := by
  rw [ofFn_split d x]
  have h : (List.ofFn (headCoefficients d x) ++ List.ofFn (tailCoefficients d x)).drop
      (List.ofFn (headCoefficients d x)).length = List.ofFn (tailCoefficients d x) :=
    List.drop_left
  simpa only [List.length_ofFn] using h

theorem zero_tail_words (p : ℕ) [Fact p.Prime] {N : ℕ}
    (d : Fin (N + 1)) (x : Fin N → ZMod p) :
    BlockZeroProgram.isZero
      ((List.ofFn fun i => MatrixWordEncoding.word p (x i)).drop d.val) =
        decide (tailCoefficients d x = 0) := by
  rw [drop_ofFn_eq_tail d (fun i => MatrixWordEncoding.word p (x i))]
  exact MatrixZeroSemantics.zero_encoded_vector p (tailCoefficients d x)

end SubexponentialSAT.Subexp.BlockSearchTailSemantics

end OAI.Algorithms
