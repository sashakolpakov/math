import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtractionStage
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingOutputSemantics

namespace OAI.Algorithms

/-! Actual generation of ascending vertex indices and the leftover scan in
the fixed packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def verticesOutputState (input : Input) (n D : ℕ) (c : PackingExtraction.Context)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 7 then AssignmentSeedRange.seedRecords D
    else (extractionOutputState input n c regs).stacks i⟩

def verticesBudget (D : ℕ) : ℕ :=
  7 * D + AssignmentSeedRange.budget D +
    6 * (AssignmentSeedRange.seedRecords D).length + 12

theorem verticesBudget_le (D : ℕ) : verticesBudget D ≤ 100 * (D + 1) ^ 2 := by
  have hb := AssignmentSeedRange.budget_le D
  have hs := ProgramEncoding.encodeRecords_length_le
    ((List.range D).map AssignmentSeedRange.unary) D (by
      intro word hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      simpa only [List.length_replicate] using Nat.le_of_lt (List.mem_range.mp hi))
  change (AssignmentSeedRange.seedRecords D).length ≤ 1 + (2 * D + 2) *
    ((List.range D).map AssignmentSeedRange.unary).length at hs
  simp only [List.length_map, List.length_range] at hs
  unfold verticesBudget
  nlinarith only [hb, hs]

private theorem vertices_call_stacks (input : Input) (n D : ℕ)
    (c : PackingExtraction.Context) (regs : Fin 16 → Bool) :
    (install (by decide : 5 ≤ 16) (by decide : 6 ≤ 48)
      (PackingPlumbing.run verticesSetup (extractionOutputState input n c regs))
      (AssignmentSeedRange.outputState D)).stacks = fun i =>
        if i = 5 then AssignmentSeedRange.seedRecords D
        else (extractionOutputState input n c regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingPlumbing.run, verticesSetup, PackingPlumbing.Op.next,
      extractionOutputState, inputState, AssignmentSeedRange.outputState,
      AssignmentSeedRange.state, StackRoutines.copyStacks, Fin.coe_ofNat_eq_mod]

theorem vertices_eval (input : Input) (n D : ℕ) (c : PackingExtraction.Context)
    (hD : input.dimension = List.replicate D true) (regs : Fin 16 → Bool) :
    ∃ steps ≤ verticesBudget D, ∃ rf,
      Eval vertices steps (extractionOutputState input n c regs)
        (verticesOutputState input n D c rf) := by
  let a := extractionOutputState input n c regs
  have hv : PackingPlumbing.Valid verticesSetup a := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, verticesSetup,
      a, extractionOutputState, inputState]
  let b := PackingPlumbing.run verticesSetup a
  have hp : project (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b =
      AssignmentSeedRange.inputState
        (project (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b).regs D := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, b, PackingPlumbing.run, verticesSetup,
        PackingPlumbing.Op.next, a, extractionOutputState, inputState, hD,

        StackRoutines.copyStacks]
  obtain ⟨nv, hnv, hvt⟩ := AssignmentSeedRange.program_runsIn
    (project (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b).regs D
  let d := install (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b
    (AssignmentSeedRange.outputState D)
  have hcall : Eval verticesCall nv b d := by
    apply lowCall_eval
    rw [hp]
    exact hvt
  have hdstacks : d.stacks = fun i =>
      if i = 5 then AssignmentSeedRange.seedRecords D
      else (extractionOutputState input n c regs).stacks i :=
    vertices_call_stacks input n D c regs
  have hw : PackingPlumbing.Valid verticesSave d := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, verticesSave,
      PackingPlumbing.move]
  let e := PackingPlumbing.run verticesSave d
  have he : e = verticesOutputState input n D c e.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [e, PackingPlumbing.run, verticesSave, PackingPlumbing.move,
        PackingPlumbing.Op.next, hdstacks, extractionOutputState,
        inputState,
        StackRoutines.transferStacks]
  have hsetup : PackingPlumbing.cost verticesSetup a = 7 * D + 5 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, verticesSetup,
      a, extractionOutputState, inputState, hD]
  have hsave : PackingPlumbing.cost verticesSave d =
      6 * (AssignmentSeedRange.seedRecords D).length + 6 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, verticesSave,
      PackingPlumbing.move, PackingPlumbing.Op.next, hdstacks,
      StackRoutines.transferStacks, extractionOutputState, inputState]
    omega
  have hrun := (PackingPlumbing.eval verticesSetup a hv).seq
    (hcall.seq (PackingPlumbing.eval verticesSave d hw))
  refine ⟨PackingPlumbing.cost verticesSetup a + (nv + PackingPlumbing.cost verticesSave d),
    ?_, e.regs, ?_⟩
  · rw [hsetup, hsave]
    unfold verticesBudget
    omega
  · change Eval vertices _ a e at hrun
    rw [he] at hrun
    exact hrun

def leftoverResult (records : PackingLeftovers.Records) (D : ℕ)
    (c : PackingExtraction.Context) : PackingLeftovers.Snapshot :=
  (List.range D).foldl (PackingLeftovers.advance records) (PackingOutputSemantics.snapshotOf c)

theorem leftoverResult_eq_finish {V U : Type*} [DecidableEq V] [DecidableEq U]
    (P : ConstructivePacking.PackingData V U) (code : V → ℕ)
    (encodeType : U → List Bool) (D : ℕ) (c : PackingExtraction.Context)
    (horder : P.vertices.values.map code = List.range D) :
    leftoverResult
        (PackingMetadata.coveredRecords P (PackingOutputSemantics.vertexBytes code) encodeType) D c =
      PackingOutputSemantics.finish P code encodeType (PackingOutputSemantics.snapshotOf c) := by
  simp only [leftoverResult, PackingOutputSemantics.finish, horder]

def leftoversBudget (records : PackingLeftovers.Records) (D : ℕ)
    (c : PackingExtraction.Context) : ℕ :=
  let result := leftoverResult records D c
  PackingLeftovers.traceCost records (List.range D) (PackingOutputSemantics.snapshotOf c) +
    6 * result.rank + 6 * result.metadata.length + 6 * result.addresses.length +
    3 * result.storage.length + 2 * (SelectorProgram.rawRecords records).length +
    2 * result.address + 32

private theorem leftovers_call_stacks (input : Input) (n D : ℕ)
    (c : PackingExtraction.Context) (records : PackingLeftovers.Records)
    (result : PackingLeftovers.Snapshot) (regs : Fin 16 → Bool) (rl : Fin 8 → Bool) :
    (install (by decide : 8 ≤ 16) (by decide : 18 ≤ 48)
      (verticesOutputState input n D c regs)
      (PackingLeftovers.state rl (SelectorProgram.rawRecords records) []
        (PackingLeftovers.unary result.rank) (PackingLeftovers.unary result.address)
        result.storage result.metadata result.addresses)).stacks = fun i =>
          if i = 6 then SelectorProgram.rawRecords records
          else if i = 10 then PackingLeftovers.unary result.rank
          else if i = 11 then PackingLeftovers.unary result.address
          else if i = 12 then result.storage
          else if i = 13 then result.metadata
          else if i = 14 then result.addresses
          else if i = 30 then List.replicate n true
          else (inputState input regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, verticesOutputState, extractionOutputState, inputState,
      PackingLeftovers.state, PackingLeftovers.data, Fin.coe_ofNat_eq_mod]

private theorem leftovers_save_stacks (input : Input) (n : ℕ)
    (records : PackingLeftovers.Records) (result : PackingLeftovers.Snapshot)
    (regs : Fin 16 → Bool) (b : Data)
    (hb : b.stacks = fun i =>
      if i = 6 then SelectorProgram.rawRecords records
      else if i = 10 then PackingLeftovers.unary result.rank
      else if i = 11 then PackingLeftovers.unary result.address
      else if i = 12 then result.storage
      else if i = 13 then result.metadata
      else if i = 14 then result.addresses
      else if i = 30 then List.replicate n true
      else (inputState input regs).stacks i) :
    (PackingPlumbing.run leftoversSave b).stacks =
      (outputState input (List.replicate n true) (List.replicate result.rank true)
        result.metadata result.addresses (result.storage.reverse ++ [false]) [] regs).stacks := by
  funext i
  by_cases hi : i ∈ ([6, 10, 11, 12, 13, 14, 31, 32, 33, 34, 35, 39] : List (Fin 48))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [PackingPlumbing.run, leftoversSave, PackingPlumbing.move,
        PackingPlumbing.Op.next, hb, inputState, outputState,
        StackRoutines.transferStacks, StackRoutines.clearStacks, TupleProgram.pushedState]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rcases hi with ⟨h6, h10, h11, h12, h13, h14, h31, h32, h33, h34, h35, h39⟩
    simp [PackingPlumbing.run, leftoversSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hb, inputState, outputState, h6, h10, h11, h12, h13, h14,
      h31, h32, h33, h34, h35, h39, StackRoutines.transferStacks, StackRoutines.clearStacks,
      TupleProgram.pushedState]

private theorem leftovers_save_cost (input : Input) (n : ℕ)
    (records : PackingLeftovers.Records) (result : PackingLeftovers.Snapshot)
    (regs : Fin 16 → Bool) (b : Data)
    (hb : b.stacks = fun i =>
      if i = 6 then SelectorProgram.rawRecords records
      else if i = 10 then PackingLeftovers.unary result.rank
      else if i = 11 then PackingLeftovers.unary result.address
      else if i = 12 then result.storage
      else if i = 13 then result.metadata
      else if i = 14 then result.addresses
      else if i = 30 then List.replicate n true
      else (inputState input regs).stacks i) :
    PackingPlumbing.cost leftoversSave b =
      6 * result.rank + 6 * result.metadata.length + 6 * result.addresses.length +
      3 * result.storage.length + 2 * (SelectorProgram.rawRecords records).length +
      2 * result.address + 32 := by
  simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, leftoversSave,
    PackingPlumbing.move, PackingPlumbing.Op.next, hb, inputState,
    StackRoutines.transferStacks, StackRoutines.clearStacks, TupleProgram.pushedState]
  omega

theorem leftovers_eval (input : Input) (n D : ℕ) (c : PackingExtraction.Context)
    (records : PackingLeftovers.Records)
    (hm : c.metadata = SelectorProgram.rawRecords records)
    (ha : c.address = List.replicate c.address.length true) (regs : Fin 16 → Bool) :
    ∃ steps ≤ leftoversBudget records D c, ∃ rf,
      Eval leftovers steps (verticesOutputState input n D c regs)
        (outputState input (List.replicate n true)
          (List.replicate (leftoverResult records D c).rank true)
          (leftoverResult records D c).metadata (leftoverResult records D c).addresses
          ((leftoverResult records D c).storage.reverse ++ [false]) [] rf) := by
  let a := verticesOutputState input n D c regs
  let initial := PackingOutputSemantics.snapshotOf c
  let result := leftoverResult records D c
  have hp : project (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a =
      PackingLeftovers.state
        (project (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a).regs
        (SelectorProgram.rawRecords records)
        (ProgramEncoding.encodeRecords ((List.range D).map PackingLeftovers.unary) ++ [])
        (PackingLeftovers.unary initial.rank) (PackingLeftovers.unary initial.address)
        initial.storage initial.metadata initial.addresses := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, a, verticesOutputState, extractionOutputState,
        inputState, AssignmentSeedRange.seedRecords,
 initial, PackingOutputSemantics.snapshotOf, hm] ; exact ha
  obtain ⟨nl, rl, hnl, hlt⟩ := PackingLeftovers.program_trace records (List.range D) initial
    (project (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a).regs []
  dsimp only [initial] at hnl
  let b := install (by decide : 8 ≤ 16) (by decide : 18 ≤ 48) a
    (PackingLeftovers.state rl (SelectorProgram.rawRecords records) []
      (PackingLeftovers.unary result.rank) (PackingLeftovers.unary result.address)
      result.storage result.metadata result.addresses)
  have hcall : Eval leftoversCall nl a b := by
    apply lowCall_eval
    rw [hp]
    exact hlt
  have hbstacks : b.stacks = fun i =>
      if i = 6 then SelectorProgram.rawRecords records
      else if i = 10 then PackingLeftovers.unary result.rank
      else if i = 11 then PackingLeftovers.unary result.address
      else if i = 12 then result.storage
      else if i = 13 then result.metadata
      else if i = 14 then result.addresses
      else if i = 30 then List.replicate n true
      else (inputState input regs).stacks i :=
    leftovers_call_stacks input n D c records result regs rl
  have hv : PackingPlumbing.Valid leftoversSave b := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, leftoversSave,
      PackingPlumbing.move]
  let d := PackingPlumbing.run leftoversSave b
  have hd : d = outputState input (List.replicate n true)
      (List.replicate result.rank true) result.metadata result.addresses
      (result.storage.reverse ++ [false]) [] d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    exact leftovers_save_stacks input n records result regs b hbstacks
  have hcost : PackingPlumbing.cost leftoversSave b =
      6 * result.rank + 6 * result.metadata.length + 6 * result.addresses.length +
      3 * result.storage.length + 2 * (SelectorProgram.rawRecords records).length +
      2 * result.address + 32 :=
    leftovers_save_cost input n records result regs b hbstacks
  have hrun := hcall.seq (PackingPlumbing.eval leftoversSave b hv)
  refine ⟨nl + PackingPlumbing.cost leftoversSave b, ?_, d.regs, ?_⟩
  · rw [hcost]
    unfold leftoversBudget
    dsimp only [result]
    omega
  · change Eval leftovers _ a d at hrun
    rw [hd] at hrun
    exact hrun

theorem vertices_leftovers_eval (input : Input) (n D : ℕ) (c : PackingExtraction.Context)
    (records : PackingLeftovers.Records) (hD : input.dimension = List.replicate D true)
    (hm : c.metadata = SelectorProgram.rawRecords records)
    (ha : c.address = List.replicate c.address.length true) (regs : Fin 16 → Bool) :
    ∃ steps ≤ verticesBudget D + leftoversBudget records D c, ∃ rf,
      Eval (.seq vertices leftovers) steps (extractionOutputState input n c regs)
        (outputState input (List.replicate n true)
          (List.replicate (leftoverResult records D c).rank true)
          (leftoverResult records D c).metadata (leftoverResult records D c).addresses
          ((leftoverResult records D c).storage.reverse ++ [false]) [] rf) := by
  obtain ⟨nv, hnv, rv, hv⟩ := vertices_eval input n D c hD regs
  obtain ⟨nl, hnl, rl, hl⟩ := leftovers_eval input n D c records hm ha rv
  exact ⟨nv + nl, Nat.add_le_add hnv hnl, rl, hv.seq hl⟩

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
