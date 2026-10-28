import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQueryCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarried

namespace OAI.Algorithms

/-! Exact-time replay of the complete denominator call. The three opaque
outer accumulators are never inspected, including by storage subroutines. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage ProgramTapeReplay

private theorem not_hidden_of_high (i : Fin 768) (hi : 340 ≤ i.val) : ¬ LeafProgram.OuterCarried.hidden i := by
  simp only [LeafProgram.OuterCarried.hidden,List.mem_cons,List.mem_nil_iff,or_false]
  intro h
  rcases h with rfl|rfl|rfl <;> norm_num [Fin.coe_ofNat_eq_mod] at hi

private theorem port_not_hidden (i : Fin 256) : ¬ LeafProgram.OuterCarried.hidden (port i) :=
  not_hidden_of_high _ (by dsimp [port]; omega)

theorem localCommand_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden localCommand := by
  refine ⟨avoids_copyMany LeafProgram.OuterCarried.hidden 460 pairs (by decide) ?_,
    avoids_call_lift_of_range LeafProgram.OuterCarried.hidden LayoutDenominatorProgram.program id port port_not_hidden,
    avoids_copyCmd LeafProgram.OuterCarried.hidden 592 728 460 (by decide) (by decide) (by decide),
    avoids_clearMany LeafProgram.OuterCarried.hidden bank ?_⟩
  · simp [pairs,LeafProgram.OuterCarried.hidden]
  · intro i hi
    exact not_hidden_of_high i ((mem_bank i).mp hi).1

/-- This is a syntactic no-read/no-write certificate for the actual fixed
40-register denominator program, not just a final-state preservation fact. -/
theorem command_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden command :=
  avoids_liftProgram LeafProgram.OuterCarried.hidden localProgram registers id
    (avoids_compiled LeafProgram.OuterCarried.hidden localCommand localCommand_avoids 740 728)

/-- Arbitrary replacement of outer accumulators preserves the exact number
of executed instructions, the registers, and every visible output tape. -/
theorem command_rebase {n : ℕ} {a b : Data} (h : Eval command n a b)
    (frame : Fin 768 → List Bool) :
    Eval command n (rebaseState LeafProgram.OuterCarried.hidden frame a) (rebaseState LeafProgram.OuterCarried.hidden frame b) :=
  eval_rebase LeafProgram.OuterCarried.hidden command_avoids h frame

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
