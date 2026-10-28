import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramKernel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistenceParity

namespace OAI.Algorithms

/-! The Walsh parity counter uses the same fixed matrix/support code as the
ternary checker. Its output is a physical unary counter, not an abstract sum. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

def binaryCell (x : ZMod 2) : Bool × Bool := (decide (x = 1), false)

theorem binaryCell_nonzero (x : ZMod 2) :
    ((binaryCell x).1 || (binaryCell x).2) = decide (x ≠ 0) := by
  fin_cases x <;> decide

theorem binaryCell_encoding (x : ZMod 2) :
    [(binaryCell x).1, (binaryCell x).2] = SubexpEnumerationPayload.scalarBits x := by
  have hw : SubexpEnumerationPayload.scalarWidth 2 = 2 := by
    norm_num [SubexpEnumerationPayload.scalarWidth]
  unfold SubexpEnumerationPayload.scalarBits
  rw [hw]
  fin_cases x <;> decide

theorem scalarFrames_binary (xs : List (ZMod 2)) :
    scalarFrames xs = framedCellStream (xs.map binaryCell) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change Encoding.frame (MatrixWordEncoding.word 2 x) ++ scalarFrames xs = _
      rw [scalarWord_eq, ← binaryCell_encoding, ih]
      rfl

theorem cellWeight_binary (xs : List (ZMod 2)) :
    cellWeight (xs.map binaryCell) = (xs.map fun x => if x ≠ 0 then 1 else 0).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, cellWeight, binaryCell_nonzero,
        decide_eq_true_eq, List.sum_cons, ih]
      omega

theorem parity_count_eval {r D : ℕ} (s : Fin D → Cayley.Cube r) (a : Cayley.Cube r)
    (regs : Fin 8 → Bool) :
    ∃ (n : ℕ) (next : State 8 16), n + 1 ≤ productSupportBudget D r ∧
      Eval productSupportCommand n (matrixInput s a regs) next ∧
      next.stacks 9 = List.replicate (WalshExistence.parityWeight s a) true ∧
      next.stacks 8 = [] := by
  obtain ⟨nm, rm, hm, ht⟩ := matrix_apply_trace s a regs
  let mid := matrixOutput s a rm
  let y := WalshExistence.parityProducts s a
  let cells := (List.ofFn y).map binaryCell
  have hw : cellWeight cells = WalshExistence.parityWeight s a := by
    rw [cellWeight_binary, List.map_ofFn, List.sum_ofFn]
    change (∑ i : Fin D, if y i ≠ 0 then 1 else 0) = _
    rw [← Finset.sum_filter]
    simp [y, WalshExistence.parityWeight]
  obtain ⟨rf, hf⟩ := framedSupport_trace cells (rm ∘ kernelRegisters) []
  let smallIn : State 4 2 := ⟨rm ∘ kernelRegisters, ![framedCellStream cells, []]⟩
  let smallOut : State 4 2 := ⟨rf, ![[], List.replicate (WalshExistence.parityWeight s a) true]⟩
  have hs : Trace framedSupportProgram (framedCellCost cells)
      (smallIn.withPC (some framedSupportProgram.entry)) (smallOut.withPC none) := by
    simpa [smallIn, smallOut, framedSupportCfg, hw] using hf
  have hin : embedState kernelRegisters kernelStacks mid smallIn = mid := by
    apply SubexpScanPrimitives.embedState_eq _ _ kernelRegisters_injective kernelStacks_injective
    · intro i; rfl
    · intro i
      fin_cases i
      · change scalarFrames (List.ofFn y) = framedCellStream cells
        exact scalarFrames_binary _
      · rfl
    · intros; rfl
    · intros; rfl
  have hc := eval_call_lifted framedSupportProgram kernelRegisters kernelStacks mid
    kernelRegisters_injective kernelStacks_injective hs
  rw [hin] at hc
  refine ⟨nm + framedCellCost cells, _, ?_, (Eval.call _ ht).seq hc, ?_, ?_⟩
  · have hcost := framedCellCost_le cells
    have hlen : cells.length = D := by simp [cells]
    rw [hlen] at hcost
    have hwidth : MatrixWordEncoding.width 2 = 2 := by
      norm_num [MatrixWordEncoding.width, SubexpLiftRing.baseWidth]
    rw [hwidth] at hm
    unfold productSupportBudget
    omega
  · exact embedState_stack _ _ mid smallOut kernelStacks_injective 1
  · exact embedState_stack _ _ mid smallOut kernelStacks_injective 0

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
