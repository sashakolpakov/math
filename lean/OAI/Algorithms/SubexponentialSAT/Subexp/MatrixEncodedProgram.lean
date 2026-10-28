import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPairProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext

namespace OAI.Algorithms

/-! Exact canonical input/output words for the two concrete matrix products. -/

namespace SubexponentialSAT.Subexp.MatrixEncodedProgram

open BitProgram BinaryArithmetic MatrixProgramSupport MatrixScalarProgram
open MatrixVectorProgram MatrixPairProgram MatrixWordEncoding
open BlockCoefficientProgram

def initial (p : ℕ) [Fact p.Prime] {m N : ℕ} (M : Fin m → Fin N → ZMod p)
    (C : Fin N → Fin N → ZMod p) (x : Fin N → ZMod p)
    (regs : Fin 8 → Bool) : StructuredProgram.State 8 20 :=
  wide (state regs [] [] (modulus p) [] [] (tableBits p C) (words (vectorWords p x))
    [] (zero p) (List.replicate N true)) (matrixBits p M)
    (List.replicate m true) [] (tableBits p C)

def final (p : ℕ) [Fact p.Prime] {m N : ℕ} (M : Fin m → Fin N → ZMod p)
    (C : Fin N → Fin N → ZMod p) (x : Fin N → ZMod p)
    (regs : Fin 8 → Bool) : StructuredProgram.State 8 20 :=
  wide (state regs [] [] (modulus p)
    (words (vectorWords p (BlockSearch.matrixMap M (BlockSearch.matrixMap C x)))) [] []
    (words (vectorWords p (BlockSearch.matrixMap C x))) [] (zero p) [])
    (matrixBits p M) (List.replicate m true) (words (vectorWords p x)) (tableBits p C)

/-- The outputs of the fixed two-product instruction table are exactly the
canonical words for `C*x` and `M*(C*x)`. No decoding or normalization oracle
appears in the executed program. -/
theorem program_trace (p : ℕ) [Fact p.Prime] {m N : ℕ}
    (M : Fin m → Fin N → ZMod p) (C : Fin N → Fin N → ZMod p)
    (x : Fin N → ZMod p) (regs : Fin 8 → Bool) :
    ∃ n ≤ MatrixPairProgram.budget m N (width p), ∃ regs',
      Trace MatrixPairProgram.program n
        ((initial p M C x regs).withPC (some MatrixPairProgram.program.entry))
        ((final p M C x regs').withPC none) := by
  obtain ⟨n, hn, rf, ys, zs, ht, hC, hM⟩ := MatrixPairProgram.program_trace
    (vectorWords p x) (matrixRows p C) (matrixRows p M) (width p)
    (modulus p) (zero p) (tableBits p C)
    (vectorWords_width p x)
    (by simpa only [vectorWords_length] using matrixRows_shape p C)
    (by simpa only [vectorWords_length] using matrixRows_shape p M)
    (by simp) (zero_length p) (zero_value p)
    (by simp) (modulus_positive p)
    (by simpa only [modulus_value] using modulus_capacity p) regs
  simp only [modulus_value] at hC hM
  have hy := MatrixProgramSemantics.matrix_result_words p C x ys hC
  change ys = vectorWords p (BlockSearch.matrixMap C x) at hy
  rw [hy] at hM
  have hz := MatrixProgramSemantics.matrix_result_words p M (BlockSearch.matrixMap C x) zs hM
  change zs = vectorWords p (BlockSearch.matrixMap M (BlockSearch.matrixMap C x)) at hz
  refine ⟨n, by simpa only [matrixRows_length, vectorWords_length] using hn, rf, ?_⟩
  simpa only [initial, final, hy, hz, matrixWords_eq_words_flatten,
    matrixRows_length, matrixBits, tableBits] using ht

end SubexponentialSAT.Subexp.MatrixEncodedProgram

end OAI.Algorithms
