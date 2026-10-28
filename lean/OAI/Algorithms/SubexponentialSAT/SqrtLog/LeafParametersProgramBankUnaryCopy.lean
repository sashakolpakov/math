import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramBank
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramSerializationUnary

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

def unaryRegs : Fin 3 → Fin 8 := Fin.castAdd 5

def unaryPorts (a o : Fin 64) : Fin 14 → Fin 77 :=
  ![port a,port o,64,65,66,67,68,69,70,71,72,73,74,75]

theorem unaryPorts_injective (a o : Fin 64) (hao : a≠o) :
    Function.Injective (unaryPorts a o) := by
  have hv : a.val≠o.val := fun h => hao (Fin.ext h)
  have ha := a.isLt
  have ho := o.isLt
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [unaryPorts,port,Fin.ext_iff]
  all_goals omega

abbrev unaryCopyCmd (a o : Fin 64) : Cmd 8 77 :=
  liftCommand (Serialization.unaryCopy 0 1) 0 1 unaryRegs (unaryPorts a o)

/-- Preserving binary-to-unary conversion in the parameter bank. The unary
output's numeric length is explicitly charged, including the lifted return. -/
theorem unaryCopy_eval (r : Regs) (w : Words) (a o : Fin 64)
    (hao : a≠o) (ho : w o=[]) :
    ∃ t rf, Eval (unaryCopyCmd a o) t (state r w)
        (state rf (Function.update w o (List.replicate (BinaryArithmetic.toNat (w a)) true))) ∧
      t ≤ Serialization.unaryCopyBound (w a)+1 := by
  let frame := state r w
  let d := projectState unaryRegs (unaryPorts a o) frame
  have hr : Function.Injective unaryRegs := Fin.castAdd_injective _ _
  have hp := unaryPorts_injective a o hao
  have hd : d.stacks 1=[] := by simpa [d,frame,projectState,unaryPorts] using ho
  have h11 : d.stacks 11=[] := by simp [d,frame,projectState,unaryPorts,state]
  have h12 : d.stacks 12=[] := by simp [d,frame,projectState,unaryPorts,state]
  have h13 : d.stacks 13=[] := by simp [d,frame,projectState,unaryPorts,state]
  obtain ⟨t,ht,he⟩ := Serialization.unaryCopy_eval 0 1 d
    (by decide) (by decide) (by decide) (by decide) hd h11 h12 h13
  have hsrc : d.stacks 0=w a := by simp [d,frame,projectState,unaryPorts]
  let u := List.replicate (BinaryArithmetic.toNat (w a)) true
  let b := embedState unaryRegs (unaryPorts a o) frame
    (SubexpClauseMastersProgram.write d 1 u)
  have he' : Eval (unaryCopyCmd a o) (t+1) frame b := by
    apply eval_liftCommand_from_state (Serialization.unaryCopy 0 1) 0 1
      unaryRegs (unaryPorts a o) frame hr hp
    simpa only [hsrc] using he
  have hbase :
      (embedState unaryRegs (unaryPorts a o) frame
        (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data)).stacks=frame.stacks := by
    change (embedState unaryRegs (unaryPorts a o) frame d).stacks=frame.stacks
    exact congrArg (fun z => z.stacks) (embedState_project unaryRegs (unaryPorts a o) frame hr hp)
  have hb : b.stacks=Function.update frame.stacks (port o) u := by
    dsimp only [b,SubexpClauseMastersProgram.write]
    rw [show (⟨SubexpClauseMastersProgram.zeroRegs,Function.update d.stacks 1 u⟩ : Serialization.Data)=
      { (⟨SubexpClauseMastersProgram.zeroRegs,d.stacks⟩ : Serialization.Data) with
        «stacks» := Function.update d.stacks 1 u } by rfl]
    rw [embedState_update_stack unaryRegs (unaryPorts a o) frame _ hp 1 u]
    exact congrArg (fun ws : Fin 77 → List Bool => Function.update ws (port o) u) hbase
  have heq : b=state b.regs (Function.update w o u) := by
    rw [← state_update r b.regs w o u]
    exact CounterForPrograms.data_ext rfl hb
  refine ⟨t+1,b.regs,?_,?_⟩
  · rw [heq] at he'
    exact he'
  · rw [hsrc] at ht
    exact Nat.add_le_add_right ht 1

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
