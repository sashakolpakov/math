import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramVariables
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup

namespace OAI.Algorithms

/-! The variable scan is started from actual serialized scopes and a mask.
The factor count is obtained by a physical record scan, never supplied as data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def zeroTotals : Totals := ⟨0,0,0,0⟩
def initial (r : Fin 10 → Bool) (scopes : List (List ℕ)) (mask : List Bool) : Data :=
  ⟨r, ![scopeBits scopes,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],mask]⟩

def factorRegs : Fin 2 → Fin 10 := Fin.castAdd 8
def factorStacks : Fin 2 → Fin 21 := ![3,1]
theorem factorRegs_injective : Function.Injective factorRegs := Fin.castAdd_injective _ _
theorem factorStacks_injective : Function.Injective factorStacks := by decide

def factorCount : Code := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram factorRegs factorStacks)

theorem factorCount_eval (r : Fin 10 → Bool) (scopes : List (List ℕ)) (mask : List Bool) :
    ∃ rf, Eval factorCount
      (SubexpSunflowerProgram.CountRecords.loopSteps (scopes.map SubexpIncidenceSlotProgram.scopeBytes))
      (copied 0 3 (initial r scopes mask))
      ⟨rf,Function.update (initial r scopes mask).stacks 1 (unary scopes.length)⟩ := by
  let a := copied 0 3 (initial r scopes mask)
  let records := scopes.map SubexpIncidenceSlotProgram.scopeBytes
  let b := SubexpScopeCountSetup.counterState false false [] (unary scopes.length)
  have heq : Encoding.encodeList id records = scopeBits scopes :=
    SubexpIncidenceSlotProgram.encode_map scopes
  have hp : projectState factorRegs factorStacks a =
      SubexpScopeCountSetup.counterState (a.regs 0) (a.regs 1) (Encoding.encodeList id records) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [a,copied,initial,StackRoutines.copyStacks,
factorStacks,ParserProgram.pair,heq]
  have ht := SubexpScopeCountSetup.counter_trace records (a.regs 0) (a.regs 1)
  simp only [records,List.length_map] at ht
  rw [←hp] at ht
  have hc := eval_call_from_state SubexpScopeCountSetup.counterProgram factorRegs factorStacks a
    factorRegs_injective factorStacks_injective (b := b) ht
  let e := embedState factorRegs factorStacks a b
  have hfinal : e = ⟨e.regs,Function.update (initial r scopes mask).stacks 1 (unary scopes.length)⟩ := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    by_cases h3 : i=3
    · subst i
      exact embedState_stack factorRegs factorStacks a b factorStacks_injective 0
    by_cases h1 : i=1
    · subst i
      exact embedState_stack factorRegs factorStacks a b factorStacks_injective 1
    · have hf := embedState_stack_frame factorRegs factorStacks a b i (by
        rintro ⟨j,hj⟩; fin_cases j <;> simp [factorStacks] at hj <;> simp_all)
      calc
        e.stacks i = a.stacks i := hf
        _ = (Function.update (initial r scopes mask).stacks 1 (unary scopes.length)) i := by
          simp [a,copied,StackRoutines.copyStacks,h3,h1]
  refine ⟨e.regs,?_⟩
  change Eval factorCount _ a e at hc
  rw [hfinal] at hc
  exact hc

def boot : Code := .seq (copy 0 3 4) (.seq factorCount (copy 20 13 4))

def bootBudget (scopes : List (List ℕ)) (mask : List Bool) :=
  7*(scopeBits scopes).length+5+
    SubexpSunflowerProgram.CountRecords.loopSteps (scopes.map SubexpIncidenceSlotProgram.scopeBytes)+
    (7*mask.length+5)

theorem boot_eval (r : Fin 10 → Bool) (scopes : List (List ℕ)) (mask : List Bool) :
    ∃ rf, Eval boot (bootBudget scopes mask) (initial r scopes mask)
      (variableState rf scopes 0 mask mask zeroTotals) := by
  have hcopy := copy_eval 0 3 4 (initial r scopes mask) (by decide) (by decide) (by decide) rfl
  obtain ⟨rc,hcount⟩ := factorCount_eval r scopes mask
  let a : Data := ⟨rc,Function.update (initial r scopes mask).stacks 1 (unary scopes.length)⟩
  have hmask := copy_eval 20 13 4 a (by decide) (by decide) (by decide) rfl
  have heq : copied 20 13 a = variableState (copied 20 13 a).regs scopes 0 mask mask zeroTotals := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i; fin_cases i <;> simp [a,initial,zeroTotals,unary,StackRoutines.copyStacks]
  rw [heq] at hmask
  refine ⟨(copied 20 13 a).regs,?_⟩
  have hcost : 7 * (scopeBits scopes).length + 5 +
      (SubexpSunflowerProgram.CountRecords.loopSteps
        (scopes.map SubexpIncidenceSlotProgram.scopeBytes) +
        (7 * mask.length + 5)) = bootBudget scopes mask := by
    simp [bootBudget, Nat.add_assoc]
  rw [← hcost]
  exact hcopy.seq (hcount.seq hmask)

def command : Code := .seq boot variableScan
def program := compiled command 0 16

theorem program_runsIn (r : Fin 10 → Bool) (scopes : List (List ℕ)) (mask : List Bool) :
    ∃ rf, RunsIn program (bootBudget scopes mask+variableBudget scopes 0 mask+2)
      ((initial r scopes mask).withPC (some program.entry))
      ((variableState rf scopes mask.length [] mask (variableTotals scopes 0 mask zeroTotals)).withPC none) := by
  obtain ⟨rb,hb⟩ := boot_eval r scopes mask
  obtain ⟨n,rf,hn,hs⟩ := variableScan_eval rb scopes 0 mask mask zeroTotals
  refine ⟨rf,bootBudget scopes mask+n+1,by omega,?_⟩
  simpa only [program, command, Nat.zero_add] using compiled_halt_trace (hb.seq hs) 0 16

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
