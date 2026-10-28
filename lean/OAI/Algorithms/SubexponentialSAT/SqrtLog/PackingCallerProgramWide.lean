import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramLayoutMasters

namespace OAI.Algorithms

/-! The caller's private64-stack workspace lies after the live native
parameter bank340..416, which must survive until ring setup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 40 768
abbrev Local := State 16 768
abbrev Code := Cmd 40 768

def registers : Fin 16 ↪ Fin 40 := ⟨Fin.castAdd 24,Fin.castAdd_injective _ _⟩
def ports : Fin 64 ↪ Fin 768 := ⟨fun i=>⟨417+i.val,by have := i.isLt; omega⟩,by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 417+i.val=417+j.val at hv
  omega⟩

@[simp] theorem ports_val (i : Fin 64) : (ports i).val = 417 + i.val := rfl

@[simp] theorem ports_eq_ports (i j : Fin 64) : ports i = ports j ↔ i = j :=
  ports.injective.eq_iff

@[simp] theorem ports_ne_low (i : Fin 64) (j : Fin 768) (hj : j.val < 417) :
    ports i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ports_val] at hv
  omega

@[simp] theorem low_ne_ports (j : Fin 768) (i : Fin 64) (hj : j.val < 417) :
    j ≠ ports i := ne_comm.mp (ports_ne_low i j hj)

@[simp] theorem ports_ne_high (i : Fin 64) (j : Fin 768) (hj : 481 ≤ j.val) :
    ports i ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [ports_val] at hv
  have hi := i.isLt
  omega

@[simp] theorem high_ne_ports (j : Fin 768) (i : Fin 64) (hj : 481 ≤ j.val) :
    j ≠ ports i := ne_comm.mp (ports_ne_high i j hj)

def project (a : Data) : Local := ⟨a.regs ∘ registers,a.stacks⟩
abbrev call (c : Cmd 16 768) : Code := .call
  (ProgramLinking.liftProgram (compiled c 684 133) registers id)

theorem call_eval (c : Cmd 16 768) (a : Data) (b : Local) (t : ℕ)
    (h : Eval c t (project a) b) :
    ∃ e, Eval (call c) (t+1) a e ∧ e.stacks=b.stacks ∧
      (∀ i : Fin 40,16 ≤ i.val → e.regs i=a.regs i) := by
  have hc := eval_call_from_state (compiled c 684 133) registers id a
    registers.injective Function.injective_id (compiled_halt_trace h 684 133)
  refine ⟨_,hc,?_,?_⟩
  · funext i
    exact embedState_stack registers id a b Function.injective_id i
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega

abbrev bankCall {L : ℕ} (p : Program 16 64 L) : Code :=
  .call (ProgramLinking.liftProgram p registers ports)

theorem bankCall_eval {L t : ℕ} (p : Program 16 64 L) (a : Data)
    (b : State 16 64)
    (h : Trace p t ((projectState registers ports a).withPC (some p.entry)) (b.withPC none)) :
    Eval (bankCall p) t a (embedState registers ports a b) :=
  eval_call_from_state p registers ports a registers.injective ports.injective h

theorem bank_frame (a : Data) (b : State 16 64) (i : Fin 768)
    (hi : i.val < 417 ∨ 481 ≤ i.val) :
    (embedState registers ports a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change 417+j.val=i.val at hv
  have := j.isLt
  omega

theorem bank_register_frame (a : Data) (b : State 16 64) (i : Fin 40)
    (hi : 16 ≤ i.val) :
    (embedState registers ports a b).regs i=a.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  have := j.isLt
  omega

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
