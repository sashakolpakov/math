import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphScan
import OAI.Algorithms.SubexponentialSAT.SubexpSetupFrames

namespace OAI.Algorithms

/-! Physical staging for one local-matrix candidate. The old matrix is
cleared, the parsed reversed candidate is restored, and the complete word
record list is copied from a persistent tape. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

abbrev GraphCandidateState := State 16 40

def graphCandidateStacks : Fin 36 → Fin 40 := Fin.castAdd 4

abbrev graphCandidatePrepare : Cmd 16 40 :=
  .seq (clearCmd 29) <|
  .seq (.call (StackRoutines.transferProgram 39 29 0 1)) (copyCmd 36 33 37)

def graphCandidatePrepared (a : GraphCandidateState) : GraphCandidateState :=
  copyState 36 33 (SubexpScanPrimitives.afterTransfer (clearState 29 a) 39 29 0 1)

def graphCandidatePrepareCost (a : GraphCandidateState) : ℕ :=
  2 * (a.stacks 29).length + 3 * (a.stacks 39).length +
    7 * (a.stacks 36).length + 11

theorem graphCandidatePrepare_eval (a : GraphCandidateState) (h25 : a.stacks 37 = []) :
    Eval graphCandidatePrepare (graphCandidatePrepareCost a) a (graphCandidatePrepared a) := by
  have hc := clear_eval 29 a
  have ht := SubexpScanPrimitives.transfer_eval (clearState 29 a)
    39 29 0 1 (by decide) (by decide)
  have htmp : (SubexpScanPrimitives.afterTransfer (clearState 29 a) 39 29 0 1).stacks 37 = [] := by
    simpa [SubexpScanPrimitives.afterTransfer, clearState, StackRoutines.transferStacks] using h25
  have hp := copy_eval 36 33 37
    (SubexpScanPrimitives.afterTransfer (clearState 29 a) 39 29 0 1)
    (by decide) (by decide) (by decide) htmp
  convert hc.seq (ht.seq hp) using 1 <;>
    simp [ graphCandidatePrepareCost, graphCandidatePrepared,
      SubexpScanPrimitives.afterTransfer, clearState, StackRoutines.transferStacks] ; omega

theorem graphCandidatePrepared_matrix {D r : ℕ}
    (Q : Fin D → Cayley.Cube r) (a : GraphCandidateState)
    (hq : a.stacks 39 = (matrixFrames Q).reverse) :
    (graphCandidatePrepared a).stacks 29 = matrixFrames Q := by
  simp [graphCandidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState, hq]

theorem graphCandidatePrepared_words (a : GraphCandidateState) (h21 : a.stacks 33 = []) :
    (graphCandidatePrepared a).stacks 33 = a.stacks 36 := by
  simp [graphCandidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState, h21]

theorem graphCandidatePrepared_payload (a : GraphCandidateState) :
    (graphCandidatePrepared a).stacks 39 = [] := by
  simp [graphCandidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState]

theorem graphCandidatePrepared_frame (a : GraphCandidateState) (i : Fin 40)
    (h18 : i ≠ 29) (h21 : i ≠ 33) (h27 : i ≠ 39) :
    (graphCandidatePrepared a).stacks i = a.stacks i := by
  simp [graphCandidatePrepared, copyState, StackRoutines.copyStacks,
    SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, clearState,
    h18,h21,h27]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
