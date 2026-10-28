import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSemantics

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

def scalarFrames {p : ℕ} [Fact p.Prime] (xs : List (ZMod p)) : List Bool :=
  MatrixProgramSupport.words (xs.map (MatrixWordEncoding.word p))

def matrixFrames {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) : List Bool :=
  MatrixVectorProgram.matrixWords
    (List.ofFn fun i => List.ofFn fun j => MatrixWordEncoding.word p (Q i j))

def matrixInput {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p)
    (regs : Fin 8 → Bool) : State 8 16 :=
  MatrixScalarProgram.state regs [] [] (MatrixWordEncoding.modulus p) [] []
    (matrixFrames Q) (scalarFrames (List.ofFn x)) []
    (MatrixWordEncoding.zero p) (List.replicate t true)

def matrixOutput {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p)
    (regs : Fin 8 → Bool) : State 8 16 :=
  MatrixScalarProgram.state regs [] [] (MatrixWordEncoding.modulus p)
    (scalarFrames (List.ofFn fun i => ∑ j, Q i j * x j)) [] []
    (scalarFrames (List.ofFn x)) [] (MatrixWordEncoding.zero p) []

theorem scalarWord_eq (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    MatrixWordEncoding.word p x = SubexpEnumerationPayload.scalarBits x := by
  simp [MatrixWordEncoding.word, MatrixWordEncoding.width, SubexpLiftRing.baseWidth,
    SubexpEnumerationPayload.scalarBits, SubexpEnumerationPayload.scalarWidth]

/-- The field result is connected to the exact bytes produced by the program.
The theorem includes parsing, every failed or successful arithmetic step,
the runtime row loop, and reversal into forward output order. -/
theorem matrix_apply_trace {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p) (regs : Fin 8 → Bool) :
    ∃ n rf, n ≤ MatrixVectorProgram.matrixBudget t D (MatrixWordEncoding.width p) ∧
      Trace MatrixVectorProgram.matrixProgram n
        ((matrixInput Q x regs).withPC (some MatrixVectorProgram.matrixProgram.entry))
        ((matrixOutput Q x rf).withPC none) := by
  have hx : ∀ w ∈ (List.ofFn fun j => MatrixWordEncoding.word p (x j)),
      w.length = MatrixWordEncoding.width p := by
    intro w hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
    exact MatrixWordEncoding.word_length p _
  have hrows : ∀ row ∈ (List.ofFn fun i =>
      List.ofFn fun j => MatrixWordEncoding.word p (Q i j)),
      (List.ofFn fun j => MatrixWordEncoding.word p (x j)).length = row.length ∧
      ∀ w ∈ row, w.length = MatrixWordEncoding.width p := by
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    constructor
    · simp
    · intro w hw
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      exact MatrixWordEncoding.word_length p _
  obtain ⟨n, hn, rf, results, ht, hrel⟩ := MatrixVectorProgram.matrix_trace
    (List.ofFn fun j => MatrixWordEncoding.word p (x j))
    (List.ofFn fun i => List.ofFn fun j => MatrixWordEncoding.word p (Q i j))
    (MatrixWordEncoding.width p) (MatrixWordEncoding.modulus p) (MatrixWordEncoding.zero p)
    hx hrows (MatrixWordEncoding.zero_length p) (MatrixWordEncoding.zero_value p)
    (MatrixWordEncoding.modulus_length p).le (MatrixWordEncoding.modulus_positive p)
    (by rw [MatrixWordEncoding.modulus_value]; exact MatrixWordEncoding.modulus_capacity p)
    regs []
  rw [MatrixWordEncoding.modulus_value] at hrel
  have heq := MatrixProgramSemantics.matrix_result_words p Q x results hrel
  refine ⟨n, rf, by simpa using hn, ?_⟩
  simpa [matrixInput, matrixOutput, matrixFrames, scalarFrames, heq,
    List.map_ofFn, Function.comp_def] using ht

theorem matrix_apply_primitive {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p) (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (primitive MatrixVectorProgram.matrixProgram).step
      (primitiveOverhead MatrixVectorProgram.matrixProgram *
        MatrixVectorProgram.matrixBudget t D (MatrixWordEncoding.width p))
      (primitiveCfg MatrixVectorProgram.matrixProgram
        ((matrixInput Q x regs).withPC (some MatrixVectorProgram.matrixProgram.entry)))
      (primitiveCfg MatrixVectorProgram.matrixProgram ((matrixOutput Q x rf).withPC none)) := by
  obtain ⟨n, rf, hn, ht⟩ := matrix_apply_trace Q x regs
  exact ⟨rf, primitive_execution MatrixVectorProgram.matrixProgram ⟨n, hn, ht⟩⟩

theorem scalarFrames_ternary (xs : List SparseCode.F3) :
    scalarFrames xs = framedCellStream (xs.map ternaryCell) := by
  rw [framedCellStream_ternary]
  simp only [scalarFrames ]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.map_cons, List.flatMap_cons, scalarWord_eq,
        MatrixProgramSupport.words] using
        congrArg (fun rest => Encoding.frame (SubexpEnumerationPayload.scalarBits x) ++ rest) ih

theorem ternary_product_weight_zero {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) (x : Fin D → SparseCode.F3) :
    SparseCode.weight (fun i => ∑ j, Q i j * x j) = 0 ↔ SparseCode.IsCodeword Q x := by
  rw [SparseCode.weight_eq_zero_iff]
  simp only [funext_iff, Pi.zero_apply, SparseCode.IsCodeword, SparseCode.check]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
