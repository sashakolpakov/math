import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgramRowScan

namespace OAI.Algorithms

/-! Paid preparation of reversed original head-ID records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def reverseRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def reversePorts : Fin 4 → Fin 288 := ![283,285,282,286]
theorem reverseRegs_injective : Function.Injective reverseRegs := Fin.castAdd_injective _ _
theorem reversePorts_injective : Function.Injective reversePorts := by decide

def reverseIDs : Code 288 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram reverseRegs reversePorts)

theorem reverseIDs_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (hb' : base 286=[]) (regs : Fin 16 → Bool) (q : Store) (js : List ℕ)
    (ht : q.todo=ids js) (hr : q.reversedIDs=[false]) :
    ∃ t ≤ 10*(ids js).length, ∃ rf, Eval reverseIDs t (state base regs q)
      (state base rf {q with todo:=[],reversedIDs:=ids js.reverse}) := by
  let records := js.map fun j => List.replicate j true
  have hproj : projectState reverseRegs reversePorts (state base regs q)=
      SubexpNormalizeProgram.filterState (regs 0) (regs 1) (regs 2)
        (Encoding.encodeList id records++[]) [] (Encoding.encodeList id []) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;>
        simp [reversePorts,state,
          SubexpPostfixControl.quadruple,records,ids,ht,hr,hb,hb',ProgramEncoding.encodeRecords,Encoding.encodeList]
  obtain ⟨t,htime,he⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] []
    (regs 0) (regs 1) (regs 2)
  rw [←hproj] at he
  have hcall := eval_call_from_state SubexpNormalizeProgram.reverseRecordsProgram reverseRegs
    reversePorts (state base regs q) reverseRegs_injective reversePorts_injective he
  let localEnd := SubexpNormalizeProgram.filterState false true false [] []
    (Encoding.encodeList id (records.reverse++[])) []
  let e := embedState reverseRegs reversePorts (state base regs q) localEnd
  have heq : e=state base e.regs {q with todo:=[],reversedIDs:=ids js.reverse} := by
    apply congrArg (StructuredProgram.State.mk e.regs)
    funext i
    by_cases hi : i ∈ Set.range reversePorts
    · obtain ⟨k,rfl⟩ := hi
      calc
        _ = localEnd.stacks k :=
          embedState_stack reverseRegs reversePorts (state base regs q) localEnd reversePorts_injective k
        _ = _ := by
          fin_cases k <;> simp [localEnd,reversePorts,SubexpNormalizeProgram.filterState,
            SubexpPostfixControl.quadruple,records,ids,hb,hb',ProgramEncoding.encodeRecords,List.map_reverse]
    · have h282 : i≠282 := fun h => hi ⟨2,by simpa [reversePorts] using h.symm⟩
      have h283 : i≠283 := fun h => hi ⟨0,by simpa [reversePorts] using h.symm⟩
      calc
        _ = (state base regs q).stacks i :=
          embedState_stack_frame reverseRegs reversePorts (state base regs q) localEnd i hi
        _ = _ := by simp [state,h282,h283]
  change Eval reverseIDs t (state base regs q) e at hcall
  rw [heq] at hcall
  exact ⟨t,htime,e.regs,hcall⟩

def copyInputIDs : Code 288 := .call (StackRoutines.copyProgram 17 283 285 0 1)
def initializeIDs : Code 288 := .seq copyInputIDs
  (.seq (Subexp.TupleProgram.pushConst 282 0 false) reverseIDs)

theorem initializeIDs_eval (base : Fin 288 → List Bool) (hb : base 285=[])
    (hb' : base 286=[]) (regs : Fin 16 → Bool) (q : Store) (js : List ℕ)
    (hi : base 17=ids js) (ht : q.todo=[]) (hr : q.reversedIDs=[]) :
    ∃ t ≤ 17*(ids js).length+7, ∃ rf, Eval initializeIDs t (state base regs q)
      (state base rf {q with todo:=[],reversedIDs:=ids js.reverse}) := by
  have hc := Subexp.TupleProgram.copy_eval (17 : Fin 288) 283 285 (0 : Fin 16) 1
    (by decide) (by decide) (by decide) (by decide) (state base regs q) (by simp [state,hb])
  let r₁ := readRegs regs 0 1 none
  let q₁ : Store := {q with todo:=ids js}
  have hceq : (⟨r₁,StackRoutines.copyStacks 17 283 (state base regs q).stacks⟩ : Data 288)=
      state base r₁ q₁ := by
    apply congrArg (StructuredProgram.State.mk r₁)
    change Function.update (state base regs q).stacks 283
      ((state base regs q).stacks 17++(state base regs q).stacks 283)=_
    simp only [state,show (17:Fin 288)≠277 by decide,show (17:Fin 288)≠278 by decide]
    change Function.update (state base regs q).stacks 283 (base 17++q.todo)=_
    rw [hi,ht,List.append_nil,update_todo]
    rfl
  change Eval copyInputIDs _ (state base regs q)
    (⟨r₁,StackRoutines.copyStacks 17 283 (state base regs q).stacks⟩ : Data 288) at hc
  rw [hceq] at hc
  have hp := Subexp.TupleProgram.pushConst_eval (282 : Fin 288) (0 : Fin 16) false (state base r₁ q₁)
  let r₂ := Function.update r₁ 0 false
  let q₂ : Store := {q₁ with reversedIDs:=[false]}
  have hpeq : Subexp.TupleProgram.pushedState 282 0 false (state base r₁ q₁)=state base r₂ q₂ := by
    apply congrArg (StructuredProgram.State.mk r₂)
    change Function.update (state base r₁ q₁).stacks 282 (false::q.reversedIDs)=_
    rw [hr,update_reversedIDs]
    rfl
  rw [hpeq] at hp
  obtain ⟨tr,htr,rf,her⟩ := reverseIDs_eval base hb hb' r₂ q₂ js rfl rfl
  refine ⟨(7*(ids js).length+5)+(2+tr),by omega,rf,?_⟩
  simpa [initializeIDs,copyInputIDs,state,hi,q₁,q₂,r₁,r₂] using hc.seq (hp.seq her)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
