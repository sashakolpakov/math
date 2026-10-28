import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramBase

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem mask_eval (regs : Fin 4 → Bool) (counter mask : List Bool) :
    ∃ n rf, n ≤ 10*mask.length+9 ∧ Eval maskStep n
      (state regs counter mask [] [] [] [] [] [] [] [])
      (state rf counter mask mask.reverse [] [] [] [] [] [] []) := by
  let a := state regs counter mask [] [] [] [] [] [] [] []
  obtain ⟨rf,hr⟩ := HighIncidenceProgram.Mask.runsIn (regs ∘ maskRegs) mask
  have ha : restrictState maskRegs maskStacks a =
      HighIncidenceProgram.Mask.state (regs ∘ maskRegs) mask [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  have hr' := transport_initial _ _ ha.symm hr
  obtain ⟨n,hn,he⟩ := lifted_call _ maskRegs maskStacks (Fin.castAdd_injective 2 2)
    (by decide) a _ _ hr'
  let rout : Fin 4 → Bool := ![rf 0,rf 1,regs 2,regs 3]
  have hb : embedState maskRegs maskStacks a
      (HighIncidenceProgram.Mask.state rf mask [] mask.reverse []) =
      state rout counter mask mask.reverse [] [] [] [] [] [] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 2 2) (by decide)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;>
        first
        | rfl
        | exact (hi ⟨0,rfl⟩).elim
        | exact (hi ⟨1,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;>
        first
        | rfl
        | exact (hi ⟨0,rfl⟩).elim
        | exact (hi ⟨1,rfl⟩).elim
        | exact (hi ⟨2,rfl⟩).elim
  have he' := Eq.mp (congrArg (fun b => Eval maskStep n a b) hb) he
  exact ⟨n,rout,hn,he'⟩

theorem copy_counter_eval (regs : Fin 4 → Bool) (counter mask forward : List Bool) :
    Eval copyCounter (7*counter.length+5)
      (state regs counter mask forward [] [] [] [] [] [] [])
      (state (readRegs regs 0 1 none) counter mask forward [] counter [] [] [] [] []) := by
  let a := state regs counter mask forward [] [] [] [] [] [] []
  have h := ListRegisterProgram.copy_run (0 : Fin 10) 4 8 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) regs a.stacks rfl
  have hs : StackRoutines.copyStacks 0 4 a.stacks =
      (state (readRegs regs 0 1 none) counter mask forward [] counter [] [] [] [] []).stacks := by
    funext i; fin_cases i <;> simp [a,state,tapes,StackRoutines.copyStacks]
  have hlen : (a.stacks 0).length = counter.length := by simp [a, state, tapes]
  rw [hs, hlen] at h
  apply Eval.call
  exact h


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
