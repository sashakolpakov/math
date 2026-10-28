import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseCost
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms
namespace SubexponentialSAT.ExecClauseCost
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Fixed register ports for the membership routine's equality subroutine. -/
def membershipEqReg (i : Fin 5) : Fin 7 := Fin.castAdd 2 i

/-- Compare caller stack 1 with caller stack 3. -/
def membershipEqStack (i : Fin 2) : Fin 5 := if i = 0 then 1 else 3

abbrev membershipEqProgram : Program 7 5 10 :=
  SubexponentialSAT.ProgramLinking.liftProgram bitEqualityProgram membershipEqReg membershipEqStack

theorem membershipEqReg_injective : Function.Injective membershipEqReg := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 7 => x.val) h

theorem membershipEqStack_injective : Function.Injective membershipEqStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [membershipEqStack]

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stkValues =>
    unfold embedState
    congr 1
    · funext i
      by_cases h : ∃ j, reg j = i
      · obtain ⟨j, rfl⟩ := h
        exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stk j = i
      · obtain ⟨j, rfl⟩ := h
        exact hs.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

/-- The actual comparator call framed in the membership routine's fixed ports.
Unassigned data is preserved, and the inspected stacks retain bounded tails. -/
theorem membershipEq_eval (d : State 7 5) :
    ∃ n ≤ 9 * ((d.stacks 1).length + 1), ∃ e : State 7 5,
      Eval (.call membershipEqProgram) n d e ∧
      e.regs 4 = decide (d.stacks 1 = d.stacks 3) ∧
      e.stacks 0 = d.stacks 0 ∧ e.stacks 2 = d.stacks 2 ∧ e.stacks 4 = d.stacks 4 ∧
      (e.stacks 1).length ≤ (d.stacks 1).length ∧
      (e.stacks 3).length ≤ (d.stacks 3).length ∧
      e.regs 5 = d.regs 5 ∧ e.regs 6 = d.regs 6 := by
  let a : State 5 2 := ⟨d.regs ∘ membershipEqReg, d.stacks ∘ membershipEqStack⟩
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout, hleft, hright⟩ :=
    bitEquality_runsIn_bounded (d.regs ∘ membershipEqReg) (d.stacks 1) (d.stacks 3)
  have ha : a.withPC (some bitEqualityProgram.entry) =
      bitEqualityStart (d.regs ∘ membershipEqReg) (d.stacks 1) (d.stacks 3) := by
    unfold a SubexponentialSAT.StructuredProgram.State.withPC bitEqualityStart bitEqualityProgram
    congr 1
    funext i
    fin_cases i <;> rfl
  have hc : (SubexponentialSAT.StructuredProgram.State.ofCfg c).withPC (none : Option (Fin 10)) = c := by
    cases c
    simp_all [SubexponentialSAT.StructuredProgram.State.ofCfg, SubexponentialSAT.StructuredProgram.State.withPC]
  have htrace : Trace bitEqualityProgram n (a.withPC (some bitEqualityProgram.entry))
      ((SubexponentialSAT.StructuredProgram.State.ofCfg c).withPC none) := by
    rw [ha, hc]
    exact ht
  have heval := eval_call_lifted bitEqualityProgram membershipEqReg membershipEqStack d
    membershipEqReg_injective membershipEqStack_injective htrace
  have hstart : embedState membershipEqReg membershipEqStack d a = d :=
    embed_restricted _ _ membershipEqReg_injective membershipEqStack_injective d
  rw [hstart] at heval
  let e := embedState membershipEqReg membershipEqStack d (SubexponentialSAT.StructuredProgram.State.ofCfg c)
  refine ⟨n, hn, e, heval, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change e.regs (membershipEqReg 4) = _
    rw [embedState_register _ _ _ _ membershipEqReg_injective]
    exact hout
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · exact embedState_stack_frame _ _ _ _ _ (by decide)
  · change (e.stacks (membershipEqStack 0)).length ≤ _
    rw [embedState_stack _ _ _ _ membershipEqStack_injective]
    exact hleft
  · change (e.stacks (membershipEqStack 1)).length ≤ _
    rw [embedState_stack _ _ _ _ membershipEqStack_injective]
    exact hright
  · exact embedState_register_frame _ _ _ _ _ (by decide)
  · exact embedState_register_frame _ _ _ _ _ (by decide)

end SubexponentialSAT.ExecClauseCost

end OAI.Algorithms
