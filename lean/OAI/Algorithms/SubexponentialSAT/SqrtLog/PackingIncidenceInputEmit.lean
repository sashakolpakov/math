import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPlanAlphabetEmit
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram

namespace OAI.Algorithms

/-! A fixed writer for one double-framed two-address incidence plan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 3 6
abbrev unary (n : ℕ) := List.replicate n true
def data (r : Fin 3 → Bool) (head factor tmp plan scratch out : List Bool) : Data :=
  ⟨r, ![head,factor,tmp,plan,scratch,out]⟩

def recordPorts : Fin 4 → Fin 6 := ![0,4,3,2]
theorem recordPorts_injective : Function.Injective recordPorts := by decide
abbrev record : Cmd 3 6 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.emitRecordProgram id recordPorts)
def recorded (d : Data) (bits : List Bool) : Data :=
  ⟨![true,false,d.regs 2], Function.update (Function.update d.stacks 2 []) 3
    (true :: (Encoding.frame bits ++ d.stacks 3))⟩

theorem record_eval (d : Data) (bits : List Bool) (hp : d.stacks 2 = bits.reverse) :
    Eval record (5*bits.length+7) d (recorded d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 4) (d.stacks 3) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 4) (true :: (Encoding.frame bits ++ d.stacks 3)) []
  have ha : embedState id recordPorts d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id recordPorts_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [a, recordPorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hp]
    · intros; rfl
  have hb : embedState id recordPorts d b = recorded d bits := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id recordPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [b, recordPorts, recorded,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple]
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨3,h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨2,h.symm⟩
      simp [recorded, h2, h3]
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id recordPorts d
    Function.injective_id recordPorts_injective
    (SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 4)
      (d.stacks 3) (d.regs 0) (d.regs 1) (d.regs 2))
  change Eval record _ (embedState id recordPorts d a) (embedState id recordPorts d b) at h
  rw [ha,hb] at h
  exact h

abbrev copy (src : Fin 6) : Cmd 3 6 := .call (StackRoutines.copyProgram src 2 4 0 1)
def copied (src : Fin 6) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src 2 d.stacks⟩
theorem copy_eval (src : Fin 6) (h2 : src ≠ 2) (h4 : src ≠ 4)
    (d : Data) (ht : d.stacks 4 = []) :
    Eval (copy src) (7*(d.stacks src).length+5) d (copied src d) :=
  TupleProgram.copy_eval src 2 4 0 1 h2 h4 (by decide) (by decide) d ht

def framePorts : Fin 3 → Fin 6 := ![3,2,5]
theorem framePorts_injective : Function.Injective framePorts := by decide
abbrev frame : Cmd 3 6 := .call
  (ProgramLinking.liftProgram SubexpPlanAlphabetEmit.program id framePorts)
def framed (d : Data) (rf : Fin 3 → Bool) (bits : List Bool) : Data :=
  ⟨rf, Function.update (Function.update (Function.update d.stacks 3 []) 2 []) 5
    (true :: Encoding.frame (Encoding.frame bits) ++ d.stacks 5)⟩

theorem frame_eval (d : Data) (ht : d.stacks 2 = []) :
    ∃ rf, Eval frame (24*(d.stacks 3).length+27) d (framed d rf (d.stacks 3)) := by
  obtain ⟨rf, h⟩ := SubexpPlanAlphabetEmit.program_trace d.regs (d.stacks 3) (d.stacks 5)
  have ha : embedState id framePorts d
      (SubexpPlanAlphabetEmit.data d.regs (d.stacks 3) [] (d.stacks 5)) = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id framePorts_injective
    · intros; rfl
    · intros; rfl
    · intro i; fin_cases i <;> simp [framePorts, SubexpPlanAlphabetEmit.data, ht]
    · intros; rfl
  have hb : embedState id framePorts d
      (SubexpPlanAlphabetEmit.data rf [] []
        (true :: Encoding.frame (Encoding.frame (d.stacks 3)) ++ d.stacks 5)) =
      framed d rf (d.stacks 3) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id framePorts_injective
    · intros; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [framePorts, SubexpPlanAlphabetEmit.data, framed]
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨1,h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨0,h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨2,h.symm⟩
      simp [framed, h2, h3, h5]
  have he := eval_call_lifted SubexpPlanAlphabetEmit.program id framePorts d
    Function.injective_id framePorts_injective h
  exact ⟨rf, by simpa only [ha, hb] using he⟩

abbrev command : Cmd 3 6 := .seq (TupleProgram.pushConst 3 0 false)
  (.seq (copy 1) (.seq record (.seq (copy 0) (.seq record frame))))
def plan (h f : ℕ) : List Bool := CollisionStreamProgram.planBytes [h,f]

theorem command_eval (r : Fin 3 → Bool) (h f : ℕ) (out : List Bool) :
    ∃ rf, Eval command (60*(h+f)+173)
      (data r (unary h) (unary f) [] [] [] out)
      (data rf (unary h) (unary f) [] [] []
        (true :: Encoding.frame (Encoding.frame (plan h f)) ++ out)) := by
  let a := data r (unary h) (unary f) [] [] [] out
  let b := TupleProgram.pushedState 3 0 false a
  let c := copied 1 b
  let d := recorded c (unary f)
  let e := copied 0 d
  let g := recorded e (unary h)
  have h1 := TupleProgram.pushConst_eval (3 : Fin 6) (0 : Fin 3) false a
  have h2 := copy_eval 1 (by decide) (by decide) b (by simp [b,a,data])
  have h3 := record_eval c (unary f) (by simp [c,copied,b,a,data,StackRoutines.copyStacks])
  have h4 := copy_eval 0 (by decide) (by decide) d (by simp [d,recorded,c,copied,b,a,data,StackRoutines.copyStacks])
  have h5 := record_eval e (unary h) (by simp [e,copied,d,recorded,c,copied,b,a,data,StackRoutines.copyStacks])
  obtain ⟨rf,h6⟩ := frame_eval g (by simp [g,recorded])
  have hp : g.stacks 3 = plan h f := by
    simp [g,recorded,e,copied,d,c,b,a,data,StackRoutines.copyStacks,
      plan,CollisionStreamProgram.planBytes,ProgramEncoding.encodeRecords,
      Encoding.encodeList, GatherProgram.indexRecords ]
  have he : framed g rf (g.stacks 3) =
      data rf (unary h) (unary f) [] [] []
        (true :: Encoding.frame (Encoding.frame (plan h f)) ++ out) := by
    apply congrArg (StructuredProgram.State.mk rf)
    funext i; fin_cases i <;>
      simp [g,recorded,e,copied,d,c,b,a,data,
        StackRoutines.copyStacks,plan,CollisionStreamProgram.planBytes,
        ProgramEncoding.encodeRecords,Encoding.encodeList,GatherProgram.indexRecords]
  have hc : (plan h f).length = 2*(h+f)+5 := by
    simp [plan,CollisionStreamProgram.planBytes,ProgramEncoding.encodeRecords,
      Encoding.encodeList,Encoding.length_frame,GatherProgram.indexRecords]
    omega
  have hh := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  rw [he] at hh
  refine ⟨rf, ?_⟩
  convert hh using 1 ;
    simp [c,copied,b,a,data,StackRoutines.copyStacks,
      d,recorded,hp,hc] ; ring
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Emit

end OAI.Algorithms
