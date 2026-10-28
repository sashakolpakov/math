import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramArithmetic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem compareStacks_injective : Function.Injective compareStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [compareStacks]

theorem belowClauseCount_eval (d : Data)
    (hw : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[]) :
    ∃ rf, Eval belowClauseCount (52*((d.stacks 21).length+(d.stacks 4).length)+54)
      d ⟨rf,d.stacks⟩ ∧
      (rf 7=true ↔ BinaryArithmetic.toNat (d.stacks 21) < BinaryArithmetic.toNat (d.stacks 4)) ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  have h33 : d.stacks 33=[] := hw 2 (by decide)
  have h34 : d.stacks 34=[] := hw 3 (by decide)
  have h35 : d.stacks 35=[] := hw 4 (by decide)
  have h36 : d.stacks 36=[] := hw 5 (by decide)
  have h37 : d.stacks 37=[] := hw 6 (by decide)
  have h38 : d.stacks 38=[] := hw 7 (by decide)
  obtain ⟨rr,he,hflag⟩ := Compare.command_eval (d.regs ∘ low8) (d.stacks 21) (d.stacks 4)
  let a := SaturatingSubtractionProgram.state (d.regs ∘ low8) (d.stacks 21) (d.stacks 4) []
  let b := SaturatingSubtractionProgram.state rr (d.stacks 21) (d.stacks 4) []
  have hin : embedState low8 compareStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective compareStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [a,
        compareStacks,h33,h34,h35,h36,h37,h38]
    · intro i hi; rfl
  let rf := Function.extend low8 rr d.regs
  have hout : embedState low8 compareStacks d b=(⟨rf,d.stacks⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective compareStacks_injective
    · intro i; exact low8_injective.extend_apply rr d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i
      fin_cases i <;> simp [b,
        compareStacks,h33,h34,h35,h36,h37,h38]
    · intro i hi; rfl
  have ht : Trace Compare.program (52*((d.stacks 21).length+(d.stacks 4).length)+54)
      (a.withPC (some Compare.program.entry)) (b.withPC none) := by
    convert compiled_halt_trace he 0 1 using 1
  have hl := eval_call_lifted Compare.program low8 compareStacks d
    low8_injective compareStacks_injective ht
  refine ⟨rf,by simpa only [hin,hout] using hl,?_,?_⟩
  · have h7 : rf 7=rr 7 := low8_injective.extend_apply rr d.regs 7
    simpa [h7] using hflag
  · intro i hi
    apply Function.extend_apply'
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hjlt := j.isLt
    dsimp [low8] at hv
    omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
