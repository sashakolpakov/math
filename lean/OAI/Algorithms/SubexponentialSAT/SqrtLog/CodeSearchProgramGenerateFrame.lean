import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGenerate

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Generic fixed-port call of the closed generator. The result and all frame
claims refer to the actual final state of the bit program. -/
theorem generate_lifted {R S : ℕ} (p : ℕ) [Fact p.Prime]
    (register : Fin 16 → Fin R) (stack : Fin 12 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (a : State R S) (ha : GenerateReady (projectState register stack a)) :
    ∃ (n : ℕ) (out : State R S), n ≤ generateBudget p (a.stacks (stack 9)).length ∧
      Eval (liftCommand (generateCommand p) 9 10 register stack) n a out ∧
      out.stacks (stack 10) = ProgramEncoding.encodeRecords
        (framedCandidates p (a.stacks (stack 9)).length) ∧
      out.stacks (stack 9) = a.stacks (stack 9) ∧ out.stacks (stack 11) = [] ∧
      (∀ i : Fin 9, out.stacks (stack (generateStacks i)) = []) ∧
      (∀ j, (¬∃ i, stack i = j) → out.stacks j = a.stacks j) ∧
      (∀ j, (¬∃ i, register i = j) → out.regs j = a.regs j) := by
  obtain ⟨n,b,hn,he,hout,hdepth,htmp,hwork⟩ := generate_eval p (projectState register stack a) ha
  refine ⟨n+1,embedState register stack a b,hn,
    eval_liftCommand_from_state (generateCommand p) 9 10 register stack a hr hs he,?_,?_,?_,?_,?_,?_⟩
  · simpa only [projectState, Function.comp_apply,
      embedState_stack register stack a b hs 10] using hout
  · simpa only [projectState, Function.comp_apply,
      embedState_stack register stack a b hs 9] using hdepth
  · simpa only [embedState_stack register stack a b hs 11] using htmp
  · intro i
    rw [embedState_stack register stack a b hs]
    exact hwork i
  · intro j hj
    exact embedState_stack_frame register stack a b j hj
  · intro j hj
    exact embedState_register_frame register stack a b j hj

/-- Under the empty-work contract, the generator changes only its designated
output stack. Register scratch remains explicit in the frame assertion. -/
theorem generate_lifted_update {R S : ℕ} (p : ℕ) [Fact p.Prime]
    (register : Fin 16 → Fin R) (stack : Fin 12 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (a : State R S) (ha : GenerateReady (projectState register stack a)) :
    ∃ (n : ℕ) (out : State R S), n ≤ generateBudget p (a.stacks (stack 9)).length ∧
      Eval (liftCommand (generateCommand p) 9 10 register stack) n a out ∧
      out.stacks = Function.update a.stacks (stack 10)
        (ProgramEncoding.encodeRecords (framedCandidates p (a.stacks (stack 9)).length)) ∧
      (∀ j, (¬∃ i, register i = j) → out.regs j = a.regs j) := by
  obtain ⟨n,out,hn,he,hout,hd,ht,hw,hframe,hrframe⟩ :=
    generate_lifted p register stack hr hs a ha
  refine ⟨n,out,hn,he,?_,hrframe⟩
  funext j
  by_cases hj : j = stack 10
  · subst j; simpa using hout
  rw [Function.update_of_ne hj]
  by_cases hm : ∃ i, stack i = j
  · obtain ⟨i,rfl⟩ := hm
    have hi10 : i ≠ 10 := fun h => hj (congrArg stack h)
    fin_cases i
    all_goals first
      | exact (hw 0).trans (ha.1 0).symm
      | exact (hw 1).trans (ha.1 1).symm
      | exact (hw 2).trans (ha.1 2).symm
      | exact (hw 3).trans (ha.1 3).symm
      | exact (hw 4).trans (ha.1 4).symm
      | exact (hw 5).trans (ha.1 5).symm
      | exact (hw 6).trans (ha.1 6).symm
      | exact (hw 7).trans (ha.1 7).symm
      | exact (hw 8).trans (ha.1 8).symm
      | exact hd
      | exact False.elim (hi10 rfl)
      | exact ht.trans ha.2.2.symm
  · exact hframe j hm

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
