import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramLocalVerifier
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames

namespace OAI.Algorithms

/-! Physical staging for one local-matrix candidate. The old matrix is
cleared, the parsed reversed candidate is restored, and the complete word
record list is copied from a persistent tape. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

abbrev CandidateState := State 16 28

def candidateLocalStacks : Fin 24 → Fin 28 := Fin.castAdd 4

abbrev candidatePrepare : Cmd 16 28 :=
  .seq (clearCmd 18) <|
  .seq (.call (StackRoutines.transferProgram 27 18 0 1)) (copyCmd 24 21 25)

def candidatePrepared (a : CandidateState) : CandidateState :=
  copyState 24 21 (SubexpScanPrimitives.afterTransfer (clearState 18 a) 27 18 0 1)

def candidatePrepareCost (a : CandidateState) : ℕ :=
  2 * (a.stacks 18).length + 3 * (a.stacks 27).length +
    7 * (a.stacks 24).length + 11

theorem candidatePrepare_eval (a : CandidateState) (h25 : a.stacks 25 = []) :
    Eval candidatePrepare (candidatePrepareCost a) a (candidatePrepared a) := by
  have hc := clear_eval 18 a
  have ht := SubexpScanPrimitives.transfer_eval (clearState 18 a)
    27 18 0 1 (by decide) (by decide)
  have htmp : (SubexpScanPrimitives.afterTransfer (clearState 18 a) 27 18 0 1).stacks 25 = [] := by
    simpa [SubexpScanPrimitives.afterTransfer, clearState, StackRoutines.transferStacks] using h25
  have hp := copy_eval 24 21 25
    (SubexpScanPrimitives.afterTransfer (clearState 18 a) 27 18 0 1)
    (by decide) (by decide) (by decide) htmp
  convert hc.seq (ht.seq hp) using 1 <;>
    simp [ candidatePrepareCost, candidatePrepared,
      SubexpScanPrimitives.afterTransfer, clearState, StackRoutines.transferStacks] ; omega

theorem candidatePrepared_matrix {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) (a : CandidateState)
    (hq : a.stacks 27 = (matrixFrames Q).reverse) :
    (candidatePrepared a).stacks 18 = matrixFrames Q := by
  simp [candidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState, hq]

theorem candidatePrepared_words (a : CandidateState) (h21 : a.stacks 21 = []) :
    (candidatePrepared a).stacks 21 = a.stacks 24 := by
  simp [candidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState, h21]

theorem candidatePrepared_payload (a : CandidateState) :
    (candidatePrepared a).stacks 27 = [] := by
  simp [candidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState]

theorem candidatePrepared_frame (a : CandidateState) (i : Fin 28)
    (h18 : i ≠ 18) (h21 : i ≠ 21) (h27 : i ≠ 27) :
    (candidatePrepared a).stacks i = a.stacks i := by
  simp [candidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState,
    h18,h21,h27]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
