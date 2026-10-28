import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramSerializationUnary

namespace OAI.Algorithms

/-! Framing and paid parameter serialization for the packing loader. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 16 64
abbrev Code := Cmd 16 64
abbrev Store := Fin 64 → List Bool

def lowPorts : Fin 48 ↪ Fin 64 := ⟨Fin.castAdd 16, Fin.castAdd_injective _ _⟩

noncomputable def framed (outside : Store) (d : State 16 48) : Data :=
  embedState id lowPorts (⟨d.regs,outside⟩ : Data) d

@[simp] theorem framed_regs (outside : Store) (d : State 16 48) :
    (framed outside d).regs=d.regs := by
  funext i
  exact embedState_register id lowPorts (⟨d.regs,outside⟩ : Data) d Function.injective_id i

@[simp] theorem framed_low (outside : Store) (d : State 16 48) (i : Fin 48) :
    (framed outside d).stacks (lowPorts i)=d.stacks i :=
  embedState_stack id lowPorts (⟨d.regs,outside⟩ : Data) d lowPorts.injective i

theorem framed_outside (outside : Store) (d : State 16 48) (i : Fin 64)
    (hi : ¬ ∃ j, lowPorts j=i) : (framed outside d).stacks i=outside i :=
  embedState_stack_frame id lowPorts (⟨d.regs,outside⟩ : Data) d i hi

theorem framed_stack (outside : Store) (d : State 16 48) (i : Fin 64) :
    (framed outside d).stacks i =
      if h : i.val < 48 then d.stacks ⟨i.val,h⟩ else outside i := by
  by_cases hi : i.val < 48
  · let j : Fin 48 := ⟨i.val,hi⟩
    have hj : lowPorts j=i := Fin.ext rfl
    rw [← hj,framed_low]
    simp [j,lowPorts,hi]
  · have hn : ¬ ∃ j,lowPorts j=i := by
      rintro ⟨j,hj⟩
      have hval := congrArg Fin.val hj
      have := j.isLt
      change j.val=i.val at hval
      omega
    rw [framed_outside outside d i hn]
    simp [hi]

@[simp] theorem embed_framed (outside : Store) (a b : State 16 48) :
    embedState id lowPorts (framed outside a) b=framed outside b := by
  apply embedState_eq_of_ports id lowPorts _ _ b Function.injective_id lowPorts.injective
  · intro i; simp
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; exact framed_low outside b i
  · intro i hi
    rw [framed_outside outside b i hi,framed_outside outside a i hi]

/-- A low48 native program leaves all additional metadata masters intact. -/
theorem framed_call {l n : ℕ} (p : Program 16 48 l) (outside : Store)
    {a b : State 16 48}
    (h : Trace p n (a.withPC (some p.entry)) (b.withPC none)) :
    Eval (.call (ProgramLinking.liftProgram p id lowPorts)) n
      (framed outside a) (framed outside b) := by
  have he := eval_call_lifted p id lowPorts (framed outside a)
    Function.injective_id lowPorts.injective h
  simpa only [embed_framed] using he


def unaryRegs : Fin 3 ↪ Fin 16 := ⟨Fin.castAdd 13,Fin.castAdd_injective _ _⟩
def unaryCommand (ports : Fin 14 ↪ Fin 64) : Code :=
  liftCommand (LeafParametersProgram.Serialization.unaryCopy 0 1) 0 1 unaryRegs ports

/-- This is an actual binary countdown and unary emission, with its
value-dependent time bound; no numeric conversion is free. -/
theorem unaryCommand_eval (ports : Fin 14 ↪ Fin 64) (d : Data)
    (h1 : d.stacks (ports 1)=[]) (h11 : d.stacks (ports 11)=[])
    (h12 : d.stacks (ports 12)=[]) (h13 : d.stacks (ports 13)=[]) :
    ∃ t rf, Eval (unaryCommand ports) t d
      (⟨rf,Function.update d.stacks (ports 1)
        (List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks (ports 0))) true)⟩ : Data) ∧
      t ≤ LeafParametersProgram.Serialization.unaryCopyBound (d.stacks (ports 0))+1 := by
  let a := projectState unaryRegs ports d
  obtain ⟨t,ht,he⟩ := LeafParametersProgram.Serialization.unaryCopy_eval 0 1 a
    (by decide) (by decide) (by decide) (by decide) h1 h11 h12 h13
  let bits := List.replicate (SubexponentialSAT.BinaryArithmetic.toNat (d.stacks (ports 0))) true
  let b := embedState unaryRegs ports d (SubexponentialSAT.SubexpClauseMastersProgram.write a 1 bits)
  have hc : Eval (unaryCommand ports) (t+1) d b := by
    apply eval_liftCommand_from_state (LeafParametersProgram.Serialization.unaryCopy 0 1)
      0 1 unaryRegs ports d unaryRegs.injective ports.injective
    exact he
  have hbase : Function.extend ports a.stacks d.stacks=d.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project unaryRegs ports d unaryRegs.injective ports.injective)
  have hb : b.stacks=Function.update d.stacks (ports 1) bits := by
    change Function.extend ports (Function.update a.stacks 1 bits) d.stacks=_
    rw [ProgramLinking.extend_update ports.injective,hbase]
  have heq : b=(⟨b.regs,Function.update d.stacks (ports 1) bits⟩ : Data) := by
    exact SubexponentialSAT.CounterForPrograms.data_ext rfl hb
  refine ⟨t+1,b.regs,?_,Nat.add_le_add_right ht 1⟩
  rw [heq] at hc
  exact hc

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
