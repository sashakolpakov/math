import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramArithmetic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem shiftStacks_injective : Function.Injective shiftStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [shiftStacks]

theorem shiftVertex_eval (d : Data) (pairs : List (Bool × Bool)) (tail : List Bool)
    (hsource : d.stacks 1=Shift.frames (pairs.map Prod.snd)++tail)
    (hvertex : d.stacks 2=pairs.map Prod.fst)
    (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[])
    (h19 : d.stacks 19=[]) (h24 : d.stacks 24=[]) :
    ∃ rf, Eval shiftVertex (21*pairs.length+12) d
      ⟨rf,Function.update (Function.update d.stacks 1 tail) 18
        (Shift.result (d.regs 12) pairs)⟩ ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  have hc := copy_eval 2 17 d (by decide) (by decide) (by decide) h24
  let d0 := copied 2 17 d
  let d1 : Data := ⟨Function.update d0.regs 7 (d0.regs 12),d0.stacks⟩
  have hs : Eval (.base (.atom (.copy 7 12))) 1 d0 d1 := .base (.atom _ _)
  have hside : (d1.regs ∘ low8) 7=d.regs 12 := by simp [d1,d0,copied,readRegs,low8]
  obtain ⟨rr,hr,he⟩ := Shift.command_eval pairs (d.regs 12) (d1.regs ∘ low8) hside tail
  let a := Shift.state (d1.regs ∘ low8) (Shift.frames (pairs.map Prod.snd)++tail)
    (pairs.map Prod.fst) [] []
  let b := Shift.state rr tail [] [] (Shift.result (d.regs 12) pairs)
  have hin : embedState low8 shiftStacks d1 a=d1 := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective shiftStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [a,Shift.state,shiftStacks,d1,d0,copied,StackRoutines.copyStacks,
        hsource,hvertex,h17,h18,h19]
    · intro i hi; rfl
  let rf := Function.extend low8 rr d1.regs
  have hout : embedState low8 shiftStacks d1 b=
      (⟨rf,Function.update (Function.update d.stacks 1 tail) 18
        (Shift.result (d.regs 12) pairs)⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective shiftStacks_injective
    · intro i; exact low8_injective.extend_apply rr d1.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [b,Shift.state,shiftStacks,h17,h19]
    · intro i hi
      have h1i : i≠1 := fun h => hi ⟨0,by simpa [shiftStacks] using h.symm⟩
      have h17i : i≠17 := fun h => hi ⟨1,by simpa [shiftStacks] using h.symm⟩
      have h18i : i≠18 := fun h => hi ⟨3,by simpa [shiftStacks] using h.symm⟩
      simp [d1,d0,copied,StackRoutines.copyStacks,h1i,h17i,h18i]
  have ht : Trace Shift.program (14*pairs.length+6)
      (a.withPC (some Shift.program.entry)) (b.withPC none) := by
    convert compiled_halt_trace he 0 3 using 1 <;> rfl
  have hl := eval_call_lifted Shift.program low8 shiftStacks d1
    low8_injective shiftStacks_injective ht
  rw [hin,hout] at hl
  refine ⟨rf,?_,?_⟩
  · convert hc.seq (hs.seq hl) using 1
    simp [hvertex] ; omega
  · intro i hi
    have hframe : rf i=d1.regs i := by
      apply Function.extend_apply'
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      have hjlt := j.isLt
      dsimp [low8] at hv
      omega
    rw [hframe]
    have h7i : i≠7 := by
      intro h
      subst i
      change 8 ≤ 7 at hi
      omega
    simpa [d1,h7i] using copied_register 2 17 d i (by omega)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
