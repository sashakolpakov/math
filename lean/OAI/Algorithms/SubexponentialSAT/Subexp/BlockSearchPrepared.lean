import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-! The existing fixed preparation program with its clean work-port postcondition. -/

namespace SubexponentialSAT.Subexp.BlockSearchPrepared

open BitProgram StructuredCalls BlockSearchPreparation

def Clean (a : State 15 22) : Prop :=
  a.stacks 2 = [] ∧ a.stacks 3 = [] ∧ a.stacks 4 = [] ∧ a.stacks 6 = [] ∧
  a.stacks 7 = [] ∧ a.stacks 8 = [] ∧ a.stacks 9 = []

theorem program_runsIn_clean (alphabet : Records) (tableDepth vectorDepth : List Bool)
    (regs : Fin 15 → Bool) :
    ∃ next, Prepared alphabet tableDepth vectorDepth next ∧ Clean next ∧
      RunsIn program (cost alphabet tableDepth vectorDepth)
        ((inputState alphabet tableDepth vectorDepth regs).withPC (some program.entry))
        (next.withPC none) := by
  let a := inputState alphabet tableDepth vectorDepth regs
  let ta := restrictState tupleRegisters tableStacks a
  obtain ⟨tb,htb,htt⟩ := TupleProgram.generateProgram_runsIn alphabet tableDepth (ta.regs 9) ta
    (by norm_num [TupleProgram.outerInvariant,ta,a,restrictState,inputState,tableStacks,
      Fin.ext_iff,Fin.coe_ofNat_eq_mod])
    (by norm_num [ta,a,restrictState,inputState,tableStacks,Fin.ext_iff,Fin.coe_ofNat_eq_mod])
    (by norm_num [ta,a,restrictState,inputState,tableStacks,Fin.ext_iff,Fin.coe_ofNat_eq_mod])
    (by norm_num [ta,a,restrictState,inputState,tableStacks,Fin.ext_iff,Fin.coe_ofNat_eq_mod])
  let b := embedState tupleRegisters tableStacks a tb
  obtain ⟨nt,hnt,het⟩ := lifted_call TupleProgram.generateProgram tupleRegisters tableStacks
    tupleRegisters_injective tableStacks_injective a tb _ htt
  let da := restrictState dimensionRegisters dimensionStacks b
  have hds (i : Fin 5) : da.stacks i = if i = 0 then vectorDepth else [] := by
    change (embedState tupleRegisters tableStacks a tb).stacks (dimensionStacks i) = _
    rw [table_frame _ _ _ (by simp [dimensionStacks])]
    fin_cases i <;> simp [a,inputState,dimensionStacks]
  obtain ⟨db,hdb,hdt⟩ := DimensionProgram.program_runsIn_quadratic vectorDepth da
    (by simpa using hds 0) (by simpa using hds 1) (by simpa using hds 2)
    (by simpa using hds 3) (by simpa using hds 4)
  let c := embedState dimensionRegisters dimensionStacks b db
  obtain ⟨nd,hnd,hed⟩ := lifted_call DimensionProgram.program dimensionRegisters dimensionStacks
    dimensionRegisters_injective dimensionStacks_injective b db _ hdt
  let ca := restrictState tupleRegisters coefficientStacks c
  have hcs (i : Fin 9) : ca.stacks i =
      if i = 1 then ProgramEncoding.encodeRecords alphabet else if i = 8 then vectorDepth else [] := by
    change (embedState dimensionRegisters dimensionStacks b db).stacks (coefficientStacks i) = _
    rw [dimension_frame _ _ _ (by fin_cases i <;> decide)]
    fin_cases i
    · change b.stacks 14 = []
      rw [table_frame _ _ _ (by decide)]
      simp [a,inputState]
    · change (embedState tupleRegisters tableStacks a tb).stacks (tableStacks 1) = _
      rw [embedState_stack _ _ _ _ tableStacks_injective]
      simpa using htb.1.1
    all_goals
      norm_num [coefficientStacks]
      rw [table_frame _ _ _ (by decide)]
      simp [a, inputState]
  obtain ⟨cb,hcb,hct⟩ := TupleProgram.generateProgram_runsIn alphabet vectorDepth (ca.regs 9) ca
    (by simp [TupleProgram.outerInvariant,hcs]) (by simpa using hcs 0)
    (by simpa using hcs 2) (by simpa using hcs 5)
  let d := embedState tupleRegisters coefficientStacks c cb
  obtain ⟨nc,hnc,hec⟩ := lifted_call TupleProgram.generateProgram tupleRegisters coefficientStacks
    tupleRegisters_injective coefficientStacks_injective c cb _ hct
  refine ⟨d,?_,?_,nt+(nd+nc)+1,?_,StructuredCalls.compiled_halt_trace (het.seq (hed.seq hec)) 1 0⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · change (embedState tupleRegisters coefficientStacks c cb).stacks 0 = _
      rw [coefficient_frame _ _ _ (by decide) (by decide),
        dimension_frame _ _ _ (by decide)]
      change (embedState tupleRegisters tableStacks a tb).stacks (tableStacks 0) = _
      rw [embedState_stack _ _ _ _ tableStacks_injective]
      exact htb.2.1
    · change (embedState tupleRegisters coefficientStacks c cb).stacks (coefficientStacks 1) = _
      rw [embedState_stack _ _ _ _ coefficientStacks_injective]
      exact hcb.1.1
    · change (embedState tupleRegisters coefficientStacks c cb).stacks 12 = _
      rw [coefficient_frame _ _ _ (by decide) (by decide)]
      change (embedState dimensionRegisters dimensionStacks b db).stacks (dimensionStacks 3) = _
      rw [embedState_stack _ _ _ _ dimensionStacks_injective]
      exact hdb.2.2.2.1
    · change (embedState tupleRegisters coefficientStacks c cb).stacks (coefficientStacks 0) = _
      rw [embedState_stack _ _ _ _ coefficientStacks_injective]
      exact hcb.2.1
    · change (embedState tupleRegisters coefficientStacks c cb).stacks 10 = _
      rw [coefficient_frame _ _ _ (by decide) (by decide)]
      change (embedState dimensionRegisters dimensionStacks b db).stacks (dimensionStacks 1) = _
      rw [embedState_stack _ _ _ _ dimensionStacks_injective]
      exact hdb.2.1
  · have hlow (j : Fin 9) (hj : j ≠ 1) : d.stacks (tableStacks j) = tb.stacks j := by
      change (embedState tupleRegisters coefficientStacks c cb).stacks (tableStacks j) = _
      rw [coefficient_frame _ _ _ (by simp [tableStacks]; omega) (by
        intro h
        apply hj
        apply Fin.ext
        exact congrArg (fun i : Fin 22 => i.val) h)]
      rw [dimension_frame _ _ _ (Or.inl (by
        simp only [tableStacks]
        omega))]
      exact embedState_stack _ _ _ _ tableStacks_injective j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hlow 2 (by decide)).trans htb.2.2.1
    · exact (hlow 3 (by decide)).trans htb.1.2.1
    · exact (hlow 4 (by decide)).trans htb.1.2.2.1
    · exact (hlow 6 (by decide)).trans htb.1.2.2.2.1
    · exact (hlow 7 (by decide)).trans htb.1.2.2.2.2.1
    · exact (hlow 8 (by decide)).trans htb.1.2.2.2.2.2.1
    · change (embedState tupleRegisters coefficientStacks c cb).stacks 9 = []
      rw [coefficient_frame _ _ _ (by decide) (by decide)]
      change (embedState dimensionRegisters dimensionStacks b db).stacks (dimensionStacks 0) = []
      rw [embedState_stack _ _ _ _ dimensionStacks_injective]
      exact hdb.1
  · dsimp [cost]
    omega


end SubexponentialSAT.Subexp.BlockSearchPrepared

end OAI.Algorithms
