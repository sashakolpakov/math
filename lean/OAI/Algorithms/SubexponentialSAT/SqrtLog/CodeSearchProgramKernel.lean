import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramMatrix
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Physical ternary kernel membership. Matrix multiplication is followed by
the scalar-frame support counter, so its zero test does not inspect an abstract
matrix product. Both subroutines have fixed finite control. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

def kernelRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def kernelStacks : Fin 2 → Fin 16 := ![8,9]

theorem kernelRegisters_injective : Function.Injective kernelRegisters :=
  Fin.castAdd_injective _ _

theorem kernelStacks_injective : Function.Injective kernelStacks := by decide

abbrev productSupportCommand : Cmd 8 16 :=
  .seq (.call MatrixVectorProgram.matrixProgram)
    (.call (ProgramLinking.liftProgram framedSupportProgram kernelRegisters kernelStacks))

def productSupportProgram := compiled productSupportCommand 11 9

def productSupportBudget (t D : ℕ) : ℕ :=
  MatrixVectorProgram.matrixBudget t D 2 + 10 * t + 4

theorem productSupport_eval {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) (x : Fin D → SparseCode.F3)
    (regs : Fin 8 → Bool) :
    ∃ n next, n + 1 ≤ productSupportBudget t D ∧
      Eval productSupportCommand n (matrixInput Q x regs) next ∧
      next.stacks 9 = List.replicate
        (SparseCode.weight (fun i => ∑ j, Q i j * x j)) true ∧
      next.stacks 8 = [] := by
  obtain ⟨nm, rm, hm, ht⟩ := matrix_apply_trace Q x regs
  let mid := matrixOutput Q x rm
  let y : Fin t → SparseCode.F3 := fun i => ∑ j, Q i j * x j
  let cells := (List.ofFn y).map ternaryCell
  have hw : cellWeight cells = SparseCode.weight y := by
    rw [cellWeight_ternary, List.map_ofFn, List.sum_ofFn, SparseCode.weight_eq_sum]
    rfl
  obtain ⟨rf, hf⟩ := framedSupport_trace cells (rm ∘ kernelRegisters) []
  let a : State 4 2 := ⟨rm ∘ kernelRegisters, ![framedCellStream cells, []]⟩
  let b : State 4 2 := ⟨rf, ![[], List.replicate (SparseCode.weight y) true]⟩
  have hsmall : Trace framedSupportProgram (framedCellCost cells)
      (a.withPC (some framedSupportProgram.entry)) (b.withPC none) := by
    simpa [a, b, framedSupportCfg, hw] using hf
  have hin : embedState kernelRegisters kernelStacks mid a = mid := by
    apply SubexpScanPrimitives.embedState_eq _ _ kernelRegisters_injective kernelStacks_injective
    · intro i; rfl
    · intro i
      fin_cases i
      · change scalarFrames (List.ofFn y) = framedCellStream cells
        exact scalarFrames_ternary _
      · rfl
    · intros; rfl
    · intros; rfl
  have hcall := eval_call_lifted framedSupportProgram kernelRegisters kernelStacks mid
    kernelRegisters_injective kernelStacks_injective hsmall
  rw [hin] at hcall
  let next := embedState kernelRegisters kernelStacks mid b
  refine ⟨nm + framedCellCost cells, next, ?_, ?_, ?_, ?_⟩
  · have hc := framedCellCost_le cells
    have hlen : cells.length = t := by simp [cells]
    rw [hlen] at hc
    have hwidth : MatrixWordEncoding.width 3 = 2 := by
      norm_num [MatrixWordEncoding.width, SubexpLiftRing.baseWidth]
    rw [hwidth] at hm
    unfold productSupportBudget
    omega
  · exact (Eval.call _ ht).seq hcall
  · exact embedState_stack kernelRegisters kernelStacks mid b kernelStacks_injective 1
  · exact embedState_stack kernelRegisters kernelStacks mid b kernelStacks_injective 0

theorem productSupport_runsIn {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) (x : Fin D → SparseCode.F3)
    (regs : Fin 8 → Bool) :
    ∃ next : State 8 16, RunsIn productSupportProgram (productSupportBudget t D)
      ((matrixInput Q x regs).withPC (some productSupportProgram.entry))
      (next.withPC none) ∧
      (next.stacks 9 = [] ↔ SparseCode.IsCodeword Q x) ∧ next.stacks 8 = [] := by
  obtain ⟨n, next, hn, he, hout, hempty⟩ := productSupport_eval Q x regs
  refine ⟨next, ⟨n + 1, hn, compiled_halt_trace he 11 9⟩, ?_, hempty⟩
  rw [hout, List.replicate_eq_nil_iff, ternary_product_weight_zero]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
