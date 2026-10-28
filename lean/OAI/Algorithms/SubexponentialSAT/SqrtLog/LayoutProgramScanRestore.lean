import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScan
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! The old classifier parks the unary Q word on33. This wrapper physically
returns that word to22 and exposes only the two new counters and flag. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

abbrev Data := State 10 64

def scanRegisters : Fin 9 → Fin 10 := Fin.castAdd 1
def scanPorts : Fin 37 → Fin 64 := Fin.castAdd 27
abbrev scan : Cmd 10 64 := liftCommand scanStage 23 0 scanRegisters scanPorts
abbrev restore : Cmd 10 64 := .call (StackRoutines.transferProgram 33 22 0 1)
abbrev command : Cmd 10 64 := .seq scan restore

theorem scanRegisters_inj : Function.Injective scanRegisters := Fin.castAdd_injective _ _
theorem scanPorts_inj : Function.Injective scanPorts := Fin.castAdd_injective _ _

variable {r Q : ℕ}

theorem command_eval (u y : UniversalType r Q 1) (a : Data)
    (ha : projectState scanRegisters scanPorts a =
      Scan.scanInput (0 : Fin 1) u y [] [] [] [] (a.regs ∘ scanRegisters)) :
    ∃ n ≤ scanStageCost r Q 1 0+3*Q+4, ∃ e : Data,
      Eval command n a e ∧
      e.stacks = Function.update (Function.update a.stacks 2
        (List.replicate (MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows 0 u y)) true)) 3
        (List.replicate (MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows 0 u y)) true) ∧
      e.regs 7 = decide (MatrixEntryKernel.AllCompatible (0 : Fin 1) u y) := by
  let base := Scan.scanInput (0 : Fin 1) u y [] [] [] [] (a.regs ∘ scanRegisters)
  let U := MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows 0 u y)
  let H := MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows 0 u y)
  obtain ⟨ns,hns,rs,hs,hflag⟩ := Scan.scanStage_eval (0 : Fin 1) u y [] [] [] []
    (a.regs ∘ scanRegisters)
  change Eval scanStage ns base (counted base rs U H) at hs
  have hs' : Eval scanStage ns (projectState scanRegisters scanPorts a) (counted base rs U H) := by
    rw [ha]
    exact hs
  let m := embedState scanRegisters scanPorts a (counted base rs U H)
  have he := eval_liftCommand_from_state scanStage 23 0 scanRegisters scanPorts a
    scanRegisters_inj scanPorts_inj hs'
  have hslot (j : Fin 37) : a.stacks (scanPorts j) = base.stacks j :=
    congrFun (congrArg StructuredProgram.State.stacks ha) j
  have hcounted : (counted base rs U H).stacks =
      Function.update (Function.update (Function.update (Function.update base.stacks
        2 (List.replicate U true)) 3 (List.replicate H true)) 22 []) 33 (List.replicate Q true) := by
    funext j
    fin_cases j <;> simp [counted,base,Scan.scanInput,input,Function.update]
  have hbase : Function.extend scanPorts base.stacks a.stacks = a.stacks := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project scanRegisters scanPorts a scanRegisters_inj scanPorts_inj)
    rw [ha] at h
    exact h
  have hm : m.stacks = Function.update (Function.update (Function.update (Function.update
      a.stacks 2 (List.replicate U true)) 3 (List.replicate H true)) 22 [])
      33 (List.replicate Q true) := by
    change Function.extend scanPorts (counted base rs U H).stacks a.stacks = _
    rw [hcounted,ProgramLinking.extend_update scanPorts_inj,
      ProgramLinking.extend_update scanPorts_inj,ProgramLinking.extend_update scanPorts_inj,
      ProgramLinking.extend_update scanPorts_inj,hbase]
    rfl
  have hr := SubexpScanPrimitives.transfer_eval m (33 : Fin 64) 22 (0 : Fin 10) 1
    (by decide) (by decide)
  let e := SubexpScanPrimitives.afterTransfer m 33 22 0 1
  have hout : e.stacks = Function.update (Function.update a.stacks 2
      (List.replicate U true)) 3 (List.replicate H true) := by
    have h22 : a.stacks 22 = List.replicate Q true := by
      simpa [scanPorts,base,Scan.scanInput,input] using hslot 22
    have h33 : a.stacks 33 = [] := by
      simpa [scanPorts,base,Scan.scanInput,input] using hslot 33
    funext j
    by_cases h2 : j=2 <;> by_cases h3 : j=3 <;>
      by_cases h22' : j=22 <;> by_cases h33' : j=33 <;>
      simp [e,SubexpScanPrimitives.afterTransfer,StackRoutines.transferStacks,hm,
        h2,h3,h22',h33',h22,h33,Function.update]
  have hm7 : m.regs 7 = rs 7 := by
    exact embedState_register scanRegisters scanPorts a (counted base rs U H)
      scanRegisters_inj 7
  have h7 : e.regs 7 = rs 7 := by
    simpa [e,SubexpScanPrimitives.afterTransfer,readRegs] using hm7
  have spectator : MatrixEntryKernel.SpectatorsAgree (0 : Fin 1) u y := by
    intro j hj
    exact (hj (Subsingleton.elim j 0)).elim
  have hall : rs 7 = decide (MatrixEntryKernel.AllCompatible (0 : Fin 1) u y) := by
    rw [hflag]
    simpa [spectator] using MatrixEntryEvaluation.compatibility_rows (0 : Fin 1) u y
  refine ⟨(ns+1)+(3*(m.stacks 33).length+3),?_,e,he.seq hr,hout,h7.trans hall⟩
  simp only [hm,Function.update_self,List.length_replicate]
  have hns0 : ns ≤ scanStageCost r Q 1 0 := by simpa using hns
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

end OAI.Algorithms
