import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgramAuxiliary
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingAddressSemantics

namespace OAI.Algorithms

/-! The inverse read plan is constructed by actual generated vertex queries
and actual scans of the emitted address table. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def inverseQueries (D : ℕ) : List (List Bool) :=
  (List.range' 0 D).reverse.map PackingMetadata.unary

def inverseRows (records : List (List Bool × List Bool)) (D : ℕ) : List (List Bool) :=
  SelectorMapProgram.mappedRecords records (inverseQueries D)

def inverseBudget (records : List (List Bool × List Bool)) (D : ℕ) : ℕ :=
  6 * D ^ 2 + 19 * D + 33 +
  6 * (ProgramEncoding.encodeRecords (inverseQueries D)).length +
  9 * (SelectorProgram.rawRecords records).length +
  6 * (ProgramEncoding.encodeRecords (inverseRows records D)).length +
  SelectorMapProgram.budget records (inverseQueries D)

private theorem query_call_stacks (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (rq : Fin 5 → Bool) :
    (install (by decide : 5 ≤ 16) (by decide : 5 ≤ 48)
      (PackingPlumbing.run queriesSetup
        (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs))
      (⟨rq, ![[], List.replicate D true, [], ProgramEncoding.encodeRecords (inverseQueries D), []]⟩ :
        State 5 5)).stacks = fun i =>
      if i = 1 then List.replicate D true else if i = 3 then ProgramEncoding.encodeRecords (inverseQueries D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingPlumbing.run, queriesSetup, PackingPlumbing.Op.next,
      outputState, inputState, StackRoutines.copyStacks, Fin.coe_ofNat_eq_mod]

private theorem query_save_stacks (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (c : Data)
    (hc : c.stacks = fun i =>
      if i = 1 then List.replicate D true else if i = 3 then ProgramEncoding.encodeRecords (inverseQueries D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i) :
    (PackingPlumbing.run queriesSave c).stacks = fun i =>
      if i = 6 then ProgramEncoding.encodeRecords (inverseQueries D)
      else if i = 7 then SelectorProgram.rawRecords records
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [PackingPlumbing.run, queriesSave, PackingPlumbing.move, PackingPlumbing.Op.next,
      hc, outputState, inputState, StackRoutines.copyStacks, StackRoutines.transferStacks,
      StackRoutines.clearStacks]

private theorem inverse_call_stacks (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (d : Data)
    (rs : Fin 8 → Bool)
    (hd : d.stacks = fun i =>
      if i = 6 then ProgramEncoding.encodeRecords (inverseQueries D)
      else if i = 7 then SelectorProgram.rawRecords records
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i) :
    (install (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d
      (SelectorMapProgram.outputState records (inverseQueries D) rs)).stacks = fun i =>
      if i = 7 then SelectorProgram.rawRecords records
      else if i = 8 then ProgramEncoding.encodeRecords (inverseRows records D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, hd, SelectorMapProgram.outputState, SelectorMapProgram.state,
      outputState, inputState, inverseRows, Fin.coe_ofNat_eq_mod]

theorem inverse_eval (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ)
    (hD : input.dimension = List.replicate D true) (regs : Fin 16 → Bool) :
    ∃ steps ≤ inverseBudget records D, ∃ rf,
      Eval inverse steps
        (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs)
        (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage
          (ProgramEncoding.encodeRecords (inverseRows records D)) rf) := by
  let a := outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs
  let b := PackingPlumbing.run queriesSetup a
  have hv : PackingPlumbing.Valid queriesSetup a := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, queriesSetup, a, outputState, inputState]
  have h0 : (project (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b).stacks 0 =
      SubexpVertexIndexProgram.unary D := by
    simp [project, stackPorts, b, PackingPlumbing.run, queriesSetup, PackingPlumbing.Op.next,
      a, outputState, inputState, StackRoutines.copyStacks, hD]
  have hempty : ∀ i : Fin 5, i ≠ 0 →
      (project (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b).stacks i = [] := by
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    all_goals
      simp [project, stackPorts, b, PackingPlumbing.run, queriesSetup, PackingPlumbing.Op.next,
        a, outputState, inputState, StackRoutines.copyStacks]
  obtain ⟨q, hq, hready⟩ := SubexpVertexIndexProgram.program_trace D
    (project (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b)
    h0 (hempty 1 (by decide)) (hempty 2 (by decide))
    (hempty 3 (by decide)) (hempty 4 (by decide))
  let qstate : State 5 5 :=
    ⟨q.regs, ![[], List.replicate D true, [], ProgramEncoding.encodeRecords (inverseQueries D), []]⟩
  have hqe : q = qstate := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rcases hready with ⟨h0, h1, h2, h3, h4⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  rw [hqe] at hq
  let c := install (by decide : 5 ≤ 16) (by decide : 5 ≤ 48) b qstate
  have hquery : Eval queriesCall (6 * D ^ 2 + 10 * D + 5) b c :=
    lowCall_eval _ _ _ b qstate hq
  have hc : c.stacks = fun i =>
      if i = 1 then List.replicate D true else if i = 3 then ProgramEncoding.encodeRecords (inverseQueries D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i :=
    query_call_stacks input blocks leftovers metadata storage records D regs q.regs
  have hw : PackingPlumbing.Valid queriesSave c := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, queriesSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hc, outputState, inputState,
      StackRoutines.transferStacks, StackRoutines.clearStacks]
  let d := PackingPlumbing.run queriesSave c
  have hd : d.stacks = fun i =>
      if i = 6 then ProgramEncoding.encodeRecords (inverseQueries D)
      else if i = 7 then SelectorProgram.rawRecords records
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i :=
    query_save_stacks input blocks leftovers metadata storage records D regs c hc
  have hp : project (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d =
      SelectorMapProgram.inputStateWith
        (project (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d).regs records (inverseQueries D) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, hd, outputState, inputState
]
  obtain ⟨ns, hns, rs, hst⟩ := SelectorMapProgram.program_trace_from records (inverseQueries D)
    (project (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d).regs
  let e := install (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d
    (SelectorMapProgram.outputState records (inverseQueries D) rs)
  have hselect : Eval inverseCall ns d e := by
    apply lowCall_eval
    rw [hp]
    exact hst
  have hes : e.stacks = fun i =>
      if i = 7 then SelectorProgram.rawRecords records
      else if i = 8 then ProgramEncoding.encodeRecords (inverseRows records D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i :=
    inverse_call_stacks input blocks leftovers metadata storage records D regs d rs hd
  have hx : PackingPlumbing.Valid inverseSave e := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, inverseSave, PackingPlumbing.move]
  let f := PackingPlumbing.run inverseSave e
  have hf : f = outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage
      (ProgramEncoding.encodeRecords (inverseRows records D)) f.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [f, PackingPlumbing.run, inverseSave, PackingPlumbing.move, PackingPlumbing.Op.next,
        hes, outputState, inputState, StackRoutines.transferStacks, StackRoutines.clearStacks]
  have hc1 : PackingPlumbing.cost queriesSetup a = 7 * D + 5 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, queriesSetup, a, outputState, inputState, hD]
  have hc2 : PackingPlumbing.cost queriesSave c =
      6 * (ProgramEncoding.encodeRecords (inverseQueries D)).length + 2 * D +
      7 * (SelectorProgram.rawRecords records).length + 14 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, queriesSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hc, outputState, inputState,
      StackRoutines.transferStacks, StackRoutines.clearStacks] ; omega
  have hc3 : PackingPlumbing.cost inverseSave e =
      6 * (ProgramEncoding.encodeRecords (inverseRows records D)).length +
      2 * (SelectorProgram.rawRecords records).length + 9 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, inverseSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hes, outputState, inputState,
      StackRoutines.transferStacks] ; omega
  have he := (PackingPlumbing.eval queriesSetup a hv).seq
    (hquery.seq ((PackingPlumbing.eval queriesSave c hw).seq
      (hselect.seq (PackingPlumbing.eval inverseSave e hx))))
  refine ⟨PackingPlumbing.cost queriesSetup a + ((6 * D ^ 2 + 10 * D + 5) +
    (PackingPlumbing.cost queriesSave c + (ns + PackingPlumbing.cost inverseSave e))), ?_, f.regs, ?_⟩
  · rw [hc1, hc2, hc3]
    unfold inverseBudget
    omega
  · change Eval inverse _ a f at he
    rw [hf] at he
    exact he

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
