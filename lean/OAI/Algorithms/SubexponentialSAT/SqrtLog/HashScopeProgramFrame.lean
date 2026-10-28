import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Frame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

abbrev Data := State 11 25

def ports : RecordPrograms.Ports 11 25 :=
  ⟨8,9,10,23,24,by decide,by decide,by decide,by decide⟩

abbrev emit : Cmd 11 25 := .seq (pushConst 24 8 false)
  (.seq (escape ports) (pushConst 24 8 true))

def emitted (a : Data) : Data :=
  pushedState 24 8 true (escapedState ports (pushedState 24 8 false a))

theorem emit_eval (a : Data) : Eval emit (5*(a.stacks 23).length+7) a (emitted a) := by
  have h := (pushConst_eval (24 : Fin 25) (8 : Fin 11) false a).seq
    ((escape_eval_state ports (pushedState 24 8 false a)).seq
      (pushConst_eval (24 : Fin 25) (8 : Fin 11) true (escapedState ports (pushedState 24 8 false a))))
  convert h using 1 <;> simp [emitted,ports,pushedState] ; omega

abbrev fix : Cmd 11 25 := .seq (.base (.atom (.set 8 false)))
  (.seq (.base (.atom (.set 9 true))) (.base (.atom (.set 10 false))))

def fixed (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 8 false) 9 true) 10 false,a.stacks⟩

theorem fix_eval (a : Data) : Eval fix 3 a (fixed a) := by
  exact (Eval.base (.atom _ a)).seq ((Eval.base (.atom _ _)).seq (Eval.base (.atom _ _)))

abbrev command : Cmd 11 25 := .seq emit fix

theorem command_eval (a : Data) (bits : List Bool) (h : a.stacks 23=bits.reverse) :
    ∃ b : Data, Eval command (5*bits.length+10) a b ∧
      b.stacks 23=[] ∧ b.stacks 24=prependRecord bits (a.stacks 24) ∧
      b.regs 8=false ∧ b.regs 9=true ∧ b.regs 10=false ∧
      ∀ i, i ≠ 23 → i ≠ 24 → b.stacks i=a.stacks i := by
  refine ⟨fixed (emitted a),?_,?_,?_,?_,?_,?_,?_⟩
  · convert (emit_eval a).seq (fix_eval (emitted a)) using 1 ; simp [h]
  · simp [fixed,emitted,ports,pushedState]
  · simp [fixed,emitted,ports,pushedState,h,prependRecord,frame_eq_escaped,List.append_assoc]
  · simp [fixed]
  · simp [fixed]
  · simp [fixed]
  · intro i hi23 hi24
    simp [fixed,emitted,ports,pushedState,hi23,hi24]

end SubexponentialSAT.SqrtLog.HashScopeProgram.Frame

end OAI.Algorithms
