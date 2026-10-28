import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramCopy

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem merge_eval (regs : Fin 4 → Bool) (counter mask forward high : List Bool)
    (hh : high.length = HighIncidenceProgram.Restriction.highCount mask) :
    ∃ n rf, n ≤ 5*mask.length+3 ∧ Eval mergeStep n
      (state regs counter mask forward [] [] [] high mask [] [])
      (state rf counter mask forward
        (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse [] [] [] [] [] []) := by
  let a := state regs counter mask forward [] [] [] high mask [] []
  obtain ⟨rf,raw⟩ := HighIncidenceProgram.Restriction.zero_program_runsIn regs mask high [] hh
  have hfinish : HighIncidenceProgram.Restriction.state rf [] [] []
      ((HighIncidenceProgram.Restriction.zeroMerge mask high).reverse ++ []) =
      HighIncidenceProgram.Restriction.state rf [] [] []
        (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse := by rw [List.append_nil]
  have hr := Eq.mp (congrArg (fun finish =>
    RunsIn HighIncidenceProgram.Restriction.program (5*mask.length+3)
      ((HighIncidenceProgram.Restriction.state regs mask high [] []).withPC
        (some HighIncidenceProgram.Restriction.program.entry))
      (finish.withPC none)) hfinish) raw
  have ha : restrictState id mergeStacks a =
      HighIncidenceProgram.Restriction.state regs mask high [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> rfl
  have hr' := transport_initial HighIncidenceProgram.Restriction.program
    (5*mask.length+3) ha.symm hr
  obtain ⟨n,hn,he⟩ := lifted_call HighIncidenceProgram.Restriction.program id mergeStacks
    Function.injective_id (by decide) a
    (HighIncidenceProgram.Restriction.state rf [] [] []
      (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse)
    (5*mask.length+3) hr'
  have hb : embedState id mergeStacks a
      (HighIncidenceProgram.Restriction.state rf [] [] []
        (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse) =
      state rf counter mask forward (HighIncidenceProgram.Restriction.zeroMerge mask high).reverse
        [] [] [] [] [] [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id (by decide)
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;>
        first
        | rfl
        | exact (hi ⟨0,rfl⟩).elim
        | exact (hi ⟨1,rfl⟩).elim
        | exact (hi ⟨2,rfl⟩).elim
        | exact (hi ⟨3,rfl⟩).elim
  have he' := Eq.mp (congrArg (fun b => Eval mergeStep n a b) hb) he
  exact ⟨n,rf,hn,he'⟩



end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
