import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCommand
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendState

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem loadBits_eval (a : Data) (dst : Fin 768) (bits : List Bool) :
    ∃ rf, Eval (loadBits dst bits) (2*bits.length+1) a
      ⟨rf,Function.update a.stacks dst (bits++a.stacks dst)⟩ := by
  obtain ⟨rf,he⟩ := ArithmeticExpressionSupport.pushWord_eval dst bits (projectState r8 id a)
  have h := eval_liftCommand_from_state (ArithmeticExpressionSupport.pushWord dst bits) dst dst
    r8 id a (registers_injective ..) Function.injective_id he
  let b := embedState r8 id a ⟨rf,Function.update (projectState r8 id a).stacks dst
    (bits++(projectState r8 id a).stacks dst)⟩
  have hb : b = ⟨b.regs,Function.update a.stacks dst (bits++a.stacks dst)⟩ := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i
    exact embedState_stack r8 id a _ Function.injective_id i
  exact ⟨b.regs,by change Eval (loadBits dst bits) _ a b at h; rw [hb] at h; exact h⟩

def scopeResetAtoms : List (StructuredProgram.Atom 40 768) :=
  [.set 0 false,.set 1 false,.set 2 false,.set 3 false,.set 4 false,
   .set 5 false,.set 6 false,.set 7 false,.set 8 false,.set 9 false,.set 10 false]
def scopeReset (a : Data) : Data := regsState scopeResetAtoms a

theorem scopeReset_eval (a : Data) : Eval resetScopeRegs 11 a (scopeReset a) :=
  setRegs_eval scopeResetAtoms a

@[simp] theorem scopeReset_stacks (a : Data) : (scopeReset a).stacks = a.stacks := by
  rfl

theorem scopeReset_regs (a : Data) : (scopeReset a).regs ∘ r11 = HashScopeProgram.RawTable.zeroRegs := by
  funext i; fin_cases i <;> rfl

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
