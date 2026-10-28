import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryExtract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramClassify

namespace OAI.Algorithms

/-! The actual type-byte extractor and color classifier with arbitrary retained
integer caches. No finite-field arithmetic is called by this stage. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Scan

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

variable {r Q Δ : ℕ}

def scanInput (i : Fin Δ) (u y : UniversalType r Q Δ)
    (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 9 → Bool) : Data :=
  input regs (List.replicate r true) (List.replicate Q true)
    (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
    (List.replicate (i.val+1) true) (List.replicate (Q*r) true)
    cache0 cache1 cache2 cache3

theorem scanStage_eval (i : Fin Δ) (u y : UniversalType r Q Δ)
    (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 9 → Bool) :
    ∃ n ≤ scanStageCost r Q Δ i.val, ∃ out,
      Eval scanStage n (scanInput i u y cache0 cache1 cache2 cache3 regs)
        (counted (scanInput i u y cache0 cache1 cache2 cache3 regs) out
          (MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows i u y))
          (MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows i u y))) ∧
      out 7 = (decide (MatrixEntryKernel.SpectatorsAgree i u y) &&
        (MatrixEntryEvaluation.rows i u y).all MatrixScanProgram.compatible) := by
  let base := scanInput i u y cache0 cache1 cache2 cache3 regs
  let a1 := copied base 22 33
  let localRegs : Fin 8 → Bool := fun j => a1.regs (lowRegisters j)
  let a2 := install a1 (MatrixInputTypes.output i u y localRegs)
  let inner := project (by decide : 23 ≤ 37) a2
  let rows := MatrixEntryEvaluation.rows i u y
  let a3 := install a2 (MatrixScanProgram.result rows inner)
  have t0 := copy_eval base 22 33 (by decide) (by decide) (by decide)
    (by simp [base, scanInput, input])
  have hin : project (by decide : 29 ≤ 37) a1 = MatrixInputTypes.input i u y localRegs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp +decide [ a1, copied, copyStacks, base, scanInput, input
]
  obtain ⟨ni, hni, hi⟩ := MatrixInputTypes.program_runsIn i u y localRegs
  rw [← hin] at hi
  have t1 := callLow_eval MatrixInputProgram.program (by decide) a1
    (MatrixInputTypes.output i u y localRegs) hi
  have hready : MatrixScanProgram.Ready inner rows r := by
    constructor
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output, MatrixInputProgram.outputState,
        MatrixInputProgram.inputState]
    · intro j
      fin_cases j <;>
        simp +decide [inner, project, a2, install, MatrixColorReadProgram.target,
          MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState]
    · intro j
      rw [show MatrixScanProgram.streams rows =
          ![ReadPlan.encodeWord u.head, ReadPlan.encodeWord (u.slot i),
            ReadPlan.encodeWord y.head, ReadPlan.encodeWord (y.slot i)] from
              MatrixEntryEvaluation.rows_streams i u y]
      fin_cases j <;>
        simp +decide [inner, project, a2, install, MatrixColorReadProgram.source,
          MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output,
        MatrixInputProgram.outputState, MatrixInputProgram.inputState]
    · simp +decide [inner, project, a2, install, MatrixInputTypes.output,
        MatrixInputProgram.outputState, MatrixInputProgram.inputState, rows]
    · exact MatrixEntryEvaluation.rows_width i u y
  obtain ⟨ns, hns, hs⟩ := MatrixScanProgram.program_runsIn inner rows r hready
  have t2 := callLow_eval MatrixScanProgram.program (by decide) a2
    (MatrixScanProgram.result rows inner) hs
  have hstacks := MatrixScanProgram.result_stacks rows inner r hready
  have hend : a3 = counted base a3.regs
      (MatrixScanProgram.unchangedCount rows) (MatrixScanProgram.transposedCount rows) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      simp only [ hstacks]
      fin_cases j <;>
        simp +decide [ MatrixScanProgram.resultStacks, inner, project, a2, install,
          MatrixInputTypes.output, MatrixInputProgram.outputState, MatrixInputProgram.inputState,
          a1, copied, copyStacks, base, scanInput, input]
  have hflag : a3.regs 7 = (decide (MatrixEntryKernel.SpectatorsAgree i u y) &&
      rows.all MatrixScanProgram.compatible) := by
    have h7 : a3.regs 7 = (MatrixScanProgram.result rows inner).regs 7 := rfl
    rw [h7, MatrixScanProgram.result_compatible]
    simp +decide [inner, project, a2, install, MatrixInputTypes.output,
      MatrixInputProgram.outputState, MatrixEntryKernel.SpectatorsAgree]
  have he := t0.seq (t1.seq (t2.seq (Eval.base (StructuredProgram.Eval.skip a3))))
  rw [hend] at he
  refine ⟨(7 * Q + 5) + (ni + (ns + 0)), ?_, a3.regs, ?_, hflag⟩
  · simp only [rows, MatrixEntryEvaluation.rows_length] at hns
    dsimp [scanStageCost]
    omega
  · simpa [scanStage, series, base, scanInput, input] using he

end SubexponentialSAT.SqrtLog.LayoutProgram.Scan

end OAI.Algorithms
