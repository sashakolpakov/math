import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCell
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramRepresentation

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.Subexp

theorem ternary_scalarWord (x : SparseCode.F3) :
    MatrixWordEncoding.word 3 x=[decide (x=1),decide (x=2)] := by
  rw [CodeSearchProgram.scalarWord_eq]
  have hw : SubexpEnumerationPayload.scalarWidth 3=2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem ternary_frames (xs : List SparseCode.F3) :
    CodeSearchProgram.scalarFrames xs=
      xs.flatMap (fun x => Cell.frame (decide (x=1)) (decide (x=2))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Encoding.frame (MatrixWordEncoding.word 3 x) ++ CodeSearchProgram.scalarFrames xs = _
    rw [ternary_scalarWord,ih]
    rfl

theorem ternary_frames_length (xs : List SparseCode.F3) :
    (CodeSearchProgram.scalarFrames xs).length=5*xs.length := by
  rw [ternary_frames]
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Cell.frame]; omega

theorem matrixWords_flatMap (rows : List (List (List Bool))) :
    MatrixVectorProgram.matrixWords rows=rows.flatMap MatrixProgramSupport.words := by
  induction rows with
  | nil => rfl
  | cons x xs ih => simpa [MatrixVectorProgram.matrixWords] using congrArg (MatrixProgramSupport.words x++·) ih

theorem matrixFrames_rows {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) :
    CodeSearchProgram.matrixFrames Q=
      (List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).flatten := by
  rw [CodeSearchProgram.matrixFrames,matrixWords_flatMap]
  simp only [List.flatMap,CodeSearchProgram.scalarFrames,List.map_ofFn,Function.comp_def]

theorem ternary_matrixFrames_length {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3) :
    (CodeSearchProgram.matrixFrames Q).length=t*(5*D) := by
  rw [matrixFrames_rows]
  simp [List.length_flatten,Function.comp_def,ternary_frames_length]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
