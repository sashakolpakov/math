import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! The scalar loop length R−d is computed by deleting actual unary tokens.
The scan's distinguished unchanged anchor is removed first. Neither natural
subtraction nor a loop-count constructor is a machine primitive. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 2 2

abbrev ports : SubexponentialSAT.UnaryForPrograms.Ports 2 2 := ⟨1,0,1⟩
abbrev body : Cmd 2 2 := .base (.atom (.pop 0 0 1))
abbrev subtractCommand : Cmd 2 2 := SubexponentialSAT.UnaryForPrograms.forCmd ports body
abbrev command : Cmd 2 2 := .seq (SubexponentialSAT.UnaryForPrograms.popCmd ports) subtractCommand
abbrev program := compiled command 0 0

abbrev state (regs : Fin 2 → Bool) (left count : List Bool) : Data := ⟨regs,![left,count]⟩

theorem subtract_eval (regs : Fin 2 → Bool) (left count : List Bool) :
    ∃ steps ≤ 3*count.length+2, ∃ rf,
      Eval subtractCommand steps (state regs left count)
        (state rf (left.drop count.length) []) := by
  let I : ℕ → Data → Prop := fun i d => d.stacks 0 = left.drop i
  have hstable : SubexponentialSAT.UnaryForPrograms.FrameStable ports I := by
    intro i a b h ha
    change b.stacks 0 = left.drop i
    rw [← h 0 (by decide)]
    exact ha
  have hbody : SubexponentialSAT.UnaryForPrograms.BodySpec ports body I (fun _ => 1) := by
    intro i d hd
    let e := (SubexponentialSAT.StructuredProgram.Atom.pop (0:Fin 2) (0:Fin 2) 1).eval d
    refine ⟨1,e,le_rfl,.base (.atom _ _),?_,?_⟩
    · simp [e,SubexponentialSAT.StructuredProgram.Atom.eval,SubexponentialSAT.StructuredProgram.Atom.instr,
        SubexponentialSAT.StructuredProgram.State.ofCfg,execInstr]
    · change (d.stacks 0).tail = left.drop (i+1)
      rw [hd]
      exact List.tail_drop
  obtain ⟨steps,e,he,hi,hc,hcost⟩ := SubexponentialSAT.UnaryForPrograms.for_correct
    ports body I (fun _ => 1) hstable hbody (state regs left count) (by simp [I,state])
  have hout : e = state e.regs (left.drop count.length) [] := by
    apply congrArg₂ SubexponentialSAT.StructuredProgram.State.mk rfl
    funext j
    fin_cases j
    · simpa [state,I] using hi
    · simpa [state,ports] using hc
  refine ⟨steps,?_,e.regs,?_⟩
  · simp only [SubexponentialSAT.CounterForPrograms.budgetSum_const] at hcost
    simp at hcost
    omega
  · exact Eq.mp (congrArg (fun out => Eval subtractCommand steps (state regs left count) out) hout) he

/-- Removes the anchor token, then computes the required saturating length. -/
theorem command_eval (regs : Fin 2 → Bool) (R d : ℕ) :
    ∃ steps ≤ 3*d+3, ∃ rf,
      Eval command steps (state regs (List.replicate R true) (List.replicate (d+1) true))
        (state rf (List.replicate (R-d) true) []) := by
  let a := state regs (List.replicate R true) (List.replicate (d+1) true)
  let mid := SubexponentialSAT.UnaryForPrograms.popped ports a
  have hp := SubexponentialSAT.UnaryForPrograms.pop_eval ports a
  have hm : mid = state mid.regs (List.replicate R true) (List.replicate d true) := by
    apply congrArg₂ SubexponentialSAT.StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [a,ports,List.replicate_succ]
  obtain ⟨n,hn,rf,he⟩ := subtract_eval mid.regs (List.replicate R true) (List.replicate d true)
  rw [← hm] at he
  refine ⟨1+n,by simp only [List.length_replicate] at hn; omega,rf,?_⟩
  simpa [command,subtractCommand,a,List.drop_replicate] using hp.seq he

end SubexponentialSAT.SqrtLog.LayoutProgram.Count

end OAI.Algorithms
