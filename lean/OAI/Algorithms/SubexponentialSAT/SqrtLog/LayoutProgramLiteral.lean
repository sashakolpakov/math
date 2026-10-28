import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHornerProgram
import OAI.Algorithms.SubexponentialSAT.SubexpKernelControl
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! A paid preserving conversion of one scalar word into a complete forward
postfix literal. This is used for uncovered identity entries and zero branches. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Literal

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 3 4

def ports : Fin 3 → Fin 4 := Fin.castAdd 1
abbrev callLiteral : Cmd 3 4 := .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program id ports)
abbrev command : Cmd 3 4 := .seq callLiteral (.call (StackRoutines.transferProgram 1 3 0 1))
def program := compiled command 0 3

def state (regs : Fin 3 → Bool) (payload out work result : List Bool) : Data :=
  ⟨regs,![payload,out,work,result]⟩

theorem command_eval (regs : Fin 3 → Bool) (payload : List Bool) :
    ∃ rf, Eval command (14*payload.length+18)
      (state regs payload [] [] [])
      (state rf payload [] [] (SubexpKernelControl.pushWord payload)) := by
  have hr : regs=SubexpHornerProgram.triple (regs 0) (regs 1) (regs 2) := by
    funext j
    fin_cases j <;> rfl
  have ht := SubexpHornerProgram.Literal.trace payload [] (regs 0) (regs 1) (regs 2)
  let a := state regs payload [] [] []
  let b := state (SubexpHornerProgram.triple false false true) payload
    (SubexpKernelControl.pushWord payload).reverse [] []
  have he : Eval callLiteral (8*payload.length+9) a b := by
    have hp : projectState id ports a =
        ⟨SubexpHornerProgram.triple (regs 0) (regs 1) (regs 2),SubexpHornerProgram.triple payload [] []⟩ := by
      apply congrArg₂ StructuredProgram.State.mk hr
      funext j
      fin_cases j <;> rfl
    let target : State 3 3 :=
      ⟨SubexpHornerProgram.triple false false true,
        SubexpHornerProgram.triple payload ((false::Encoding.frame payload).reverse++[]) []⟩
    have ht' : Trace SubexpHornerProgram.Literal.program (8*payload.length+9)
        ((projectState id ports a).withPC (some SubexpHornerProgram.Literal.program.entry))
        (target.withPC none) := by
      rw [hp]
      simpa only [SubexpHornerProgram.Literal.cfg,StructuredProgram.State.withPC,
        SubexpHornerProgram.Literal.program,target] using ht
    have hh := eval_call_from_state SubexpHornerProgram.Literal.program id ports a
      Function.injective_id (Fin.castAdd_injective _ _) ht'
    have hb : embedState id ports a
        ⟨SubexpHornerProgram.triple false false true,
          SubexpHornerProgram.triple payload
            ((false::Encoding.frame payload).reverse++[]) []⟩=b := by
      apply embedState_eq_of_ports id ports _ _ _ Function.injective_id (Fin.castAdd_injective _ _)
      · intro j; rfl
      · intro j hj; exact (hj ⟨j,rfl⟩).elim
      · intro j; fin_cases j <;> simp [b,state,ports,SubexpHornerProgram.triple,SubexpKernelControl.pushWord]
      · intro j hj
        have hj3 : j = 3 := by
          by_contra hn
          have hlt : j.val < 3 := by omega
          exact hj ⟨⟨j.val,hlt⟩,Fin.ext rfl⟩
        subst j
        rfl
    change Eval callLiteral (8*payload.length+9) a (embedState id ports a target) at hh
    change embedState id ports a target=b at hb
    rw [hb] at hh
    exact hh
  have htr := SubexpScanPrimitives.transfer_eval b (1:Fin 4) 3 (0:Fin 3) 1 (by decide) (by decide)
  let e := SubexpScanPrimitives.afterTransfer b 1 3 0 1
  have heq : e=state e.regs payload [] [] (SubexpKernelControl.pushWord payload) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;> simp [b,state,StackRoutines.transferStacks]
  have hh := he.seq htr
  change Eval command _ a e at hh
  rw [heq] at hh
  refine ⟨e.regs,?_⟩
  convert hh using 1 ; simp [b,state,SubexpKernelControl.pushWord_length] ; omega

end SubexponentialSAT.SqrtLog.LayoutProgram.Literal

end OAI.Algorithms
