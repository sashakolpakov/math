import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramRepresentative
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding

namespace OAI.Algorithms

/-! Make the ambient zero word from the actual shape word. This is a physical
copy and padding call, not an additional promise about a cached input. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def zeroStart (regs : Fin 8 → Bool) (width outer out : List Bool) : Data :=
  ⟨regs, ![outer,[],[],[],[],[],[],[],out,[],[],[],[],[],[],[],width,[],[],[]]⟩

def paddingPorts : Fin 3 → Fin 20 := ![17,18,19]
theorem paddingPorts_injective : Function.Injective paddingPorts := by decide

def paddingCall : Code := .call (ProgramLinking.liftProgram ModularPrograms.paddingProgram id paddingPorts)
def prepareZero : Code := .seq (copy 16 17 14) paddingCall

private theorem pad_empty (width : List Bool) :
    ModularArithmetic.padTo width [] = List.replicate width.length false := by
  induction width with
  | nil => rfl
  | cons b bs ih => simpa [ModularArithmetic.padTo,List.replicate_succ] using congrArg (false :: ·) ih

theorem prepareZero_eval (regs : Fin 8 → Bool) (width outer out : List Bool) :
    ∃ rf, Eval prepareZero (11*width.length+8) (zeroStart regs width outer out)
      (state rf width outer [] [] [] out) := by
  let d := zeroStart regs width outer out
  obtain ⟨a,ha,hsa⟩ := copy_eval (16 : Fin 20) 17 14
    (by decide) (by decide) (by decide) d rfl
  obtain ⟨rf,hr⟩ := SubexponentialSAT.SubexpDenseLiteralPadding.padding_trace_any a.regs width [] []
  have hp := pad_empty width
  have ht : Trace ModularPrograms.paddingProgram (4*width.length+3)
      ((⟨a.regs,ModularPrograms.operandStacks width [] []⟩ : State 8 3).withPC
        (some ModularPrograms.paddingProgram.entry))
      ((⟨rf,ModularPrograms.operandStacks [] [] (List.replicate width.length false)⟩ : State 8 3).withPC none) := by
    simpa [ModularPrograms.paddingCfg,ModularPrograms.paddingProgram,
      StructuredProgram.State.withPC,hp] using hr
  have hpa : projectState id paddingPorts a =
      (⟨a.regs,ModularPrograms.operandStacks width [] []⟩ : State 8 3) := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i; fin_cases i <;>
      simp [paddingPorts,ModularPrograms.operandStacks,hsa,d,zeroStart,
        StackRoutines.copyStacks]
  rw [←hpa] at ht
  have hb := eval_call_from_state ModularPrograms.paddingProgram id paddingPorts a
    Function.injective_id paddingPorts_injective ht
  let b := embedState id paddingPorts a
    (⟨rf,ModularPrograms.operandStacks [] [] (List.replicate width.length false)⟩ : State 8 3)
  have heb : b = state b.regs width outer [] [] [] out := by
    apply embedState_eq_of_ports id paddingPorts a _ _ Function.injective_id paddingPorts_injective
    · intro i; exact embedState_register id paddingPorts a _ Function.injective_id i
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi; fin_cases i <;>
        simp_all [Fin.exists_fin_succ,paddingPorts,state,d,zeroStart,StackRoutines.copyStacks]
  change Eval paddingCall (4*width.length+3) a b at hb
  rw [heb] at hb
  have hall := ha.seq hb
  refine ⟨b.regs,?_⟩
  convert hall using 1 <;> first
    | rfl
    | omega
    | (simp [d, zeroStart] ; omega)

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Representative

end OAI.Algorithms
