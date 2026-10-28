import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram

namespace OAI.Algorithms

/-! Fixed preparation of candidate tables, split dimensions, and coefficient
tuples for the universal block search. All three dimensions are runtime data. -/

namespace SubexponentialSAT.Subexp.BlockSearchPreparation

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Records := List (List Bool)

def restrictState {r s R S : ℕ} (ρ : Fin r → Fin R) (σ : Fin s → Fin S)
    (a : State R S) : State r s := ⟨a.regs ∘ ρ, a.stacks ∘ σ⟩

theorem embed_restrict_eq {r s R S : ℕ} (ρ : Fin r → Fin R) (σ : Fin s → Fin S)
    (a : State R S) (hρ : Function.Injective ρ) (hσ : Function.Injective σ) :
    embedState ρ σ a (restrictState ρ σ a) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, ρ j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_register ρ σ a (restrictState ρ σ a) hρ j
    · exact embedState_register_frame ρ σ a (restrictState ρ σ a) i h
  · funext i
    by_cases h : ∃ j, σ j = i
    · obtain ⟨j,rfl⟩ := h
      exact embedState_stack ρ σ a (restrictState ρ σ a) hσ j
    · exact embedState_stack_frame ρ σ a (restrictState ρ σ a) i h

theorem lifted_call {r s R S l : ℕ} (p : Program r s l)
    (ρ : Fin r → Fin R) (σ : Fin s → Fin S) (hρ : Function.Injective ρ)
    (hσ : Function.Injective σ) (a : State R S) (b : State r s) (bound : ℕ)
    (h : RunsIn p bound ((restrictState ρ σ a).withPC (some p.entry)) (b.withPC none)) :
    ∃ n, n ≤ bound ∧ Eval (.call (ProgramLinking.liftProgram p ρ σ)) n
      a (embedState ρ σ a b) := by
  obtain ⟨n,hn,ht⟩ := h
  refine ⟨n,hn,?_⟩
  have he := eval_call_lifted p ρ σ a hρ hσ ht
  simpa only [embed_restrict_eq ρ σ a hρ hσ] using he

def tupleRegisters (i : Fin 10) : Fin 15 := ⟨i.val, by omega⟩
def tableStacks (i : Fin 9) : Fin 22 := ⟨i.val, by omega⟩
def dimensionRegisters (i : Fin 5) : Fin 15 := ⟨i.val + 10, by omega⟩
def dimensionStacks (i : Fin 5) : Fin 22 := ⟨i.val + 9, by omega⟩
def coefficientStacks : Fin 9 → Fin 22 := ![14,1,15,16,17,18,19,20,21]

theorem tupleRegisters_injective : Function.Injective tupleRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 15 => x.val) h
theorem tableStacks_injective : Function.Injective tableStacks := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 22 => x.val) h
theorem dimensionRegisters_injective : Function.Injective dimensionRegisters := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [dimensionRegisters] at hv
  omega
theorem dimensionStacks_injective : Function.Injective dimensionStacks := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [dimensionStacks] at hv
  omega
theorem coefficientStacks_injective : Function.Injective coefficientStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [coefficientStacks]

theorem table_frame (a : State 15 22) (b : State 10 9) (i : Fin 22) (hi : 9 ≤ i.val) :
    (embedState tupleRegisters tableStacks a b).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have h := congrArg Fin.val hj
  simp only [tableStacks] at h
  omega

theorem dimension_frame (a : State 15 22) (b : State 5 5) (i : Fin 22)
    (hi : i.val < 9 ∨ 14 ≤ i.val) :
    (embedState dimensionRegisters dimensionStacks a b).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have h := congrArg Fin.val hj
  simp only [dimensionStacks] at h
  omega

theorem coefficient_frame (a : State 15 22) (b : State 10 9) (i : Fin 22)
    (hi : i.val < 14) (hi1 : i ≠ 1) :
    (embedState tupleRegisters coefficientStacks a b).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  fin_cases j <;> simp [coefficientStacks] at hj
  all_goals subst i
  all_goals omega

/-- Runtime inputs occupy alphabet 1, table depth 8, and two explicit copies
of the unary vector dimension on 9 and 21. -/
def inputState (alphabet : Records) (tableDepth vectorDepth : List Bool)
    (regs : Fin 15 → Bool) : State 15 22 :=
  ⟨regs, fun i => if i = 1 then ProgramEncoding.encodeRecords alphabet
    else if i = 8 then tableDepth
    else if i = 9 ∨ i = 21 then vectorDepth else []⟩

abbrev prepareCmd : Cmd 15 22 :=
  .seq (.call (ProgramLinking.liftProgram TupleProgram.generateProgram
      tupleRegisters tableStacks))
    (.seq (.call (ProgramLinking.liftProgram DimensionProgram.program
      dimensionRegisters dimensionStacks))
      (.call (ProgramLinking.liftProgram TupleProgram.generateProgram
        tupleRegisters coefficientStacks)))

def program := StructuredCalls.compiled prepareCmd 1 0

theorem control_size : StructuredCalls.size prepareCmd + 1 = 211 := rfl

def cost (alphabet : Records) (tableDepth vectorDepth : List Bool) : ℕ :=
  TupleProgram.powerCost alphabet tableDepth.length [[]] +
    TupleProgram.powerCost alphabet vectorDepth.length [[]] +
    6 * vectorDepth.length ^ 2 + 22 * vectorDepth.length + 36

def Prepared (alphabet : Records) (tableDepth vectorDepth : List Bool) (a : State 15 22) : Prop :=
  a.stacks 0 = ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet tableDepth.length [[]]) ∧
  a.stacks 1 = ProgramEncoding.encodeRecords alphabet ∧
  a.stacks 12 = ProgramEncoding.encodeRecords (DimensionProgram.dimensionRows 0 vectorDepth.length) ∧
  a.stacks 14 = ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet vectorDepth.length [[]]) ∧
  a.stacks 10 = List.replicate vectorDepth.length true

theorem program_runsIn (alphabet : Records) (tableDepth vectorDepth : List Bool)
    (regs : Fin 15 → Bool) :
    ∃ next, Prepared alphabet tableDepth vectorDepth next ∧
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
      simp [a,inputState]
  obtain ⟨cb,hcb,hct⟩ := TupleProgram.generateProgram_runsIn alphabet vectorDepth (ca.regs 9) ca
    (by simp [TupleProgram.outerInvariant,hcs]) (by simpa using hcs 0)
    (by simpa using hcs 2) (by simpa using hcs 5)
  let d := embedState tupleRegisters coefficientStacks c cb
  obtain ⟨nc,hnc,hec⟩ := lifted_call TupleProgram.generateProgram tupleRegisters coefficientStacks
    tupleRegisters_injective coefficientStacks_injective c cb _ hct
  refine ⟨d,?_,nt+(nd+nc)+1,?_,StructuredCalls.compiled_halt_trace (het.seq (hed.seq hec)) 1 0⟩
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
  · dsimp [cost]
    omega

theorem program_primitive_runsIn (alphabet : Records) (tableDepth vectorDepth : List Bool)
    (regs : Fin 15 → Bool) :
    ∃ next, Prepared alphabet tableDepth vectorDepth next ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * cost alphabet tableDepth vectorDepth)
        (BitProgram.primitiveCfg program
          ((inputState alphabet tableDepth vectorDepth regs).withPC (some program.entry)))
        (BitProgram.primitiveCfg program (next.withPC none)) := by
  obtain ⟨next,hp,hr⟩ := program_runsIn alphabet tableDepth vectorDepth regs
  exact ⟨next,hp,BitProgram.primitive_execution program hr⟩

end SubexponentialSAT.Subexp.BlockSearchPreparation

end OAI.Algorithms
