import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan
import OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

open BitProgram StackRoutines StructuredCalls

abbrev Data := StructuredProgram.State 5 13

private theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

private theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply state_ext
  · funext j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

def equalityPorts : Fin 2 → Fin 13 := fun i => if i = 0 then 1 else 12

theorem equalityPorts_injective : Function.Injective equalityPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [equalityPorts]

abbrev equalityProgram : Program 5 13 10 :=
  ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram id equalityPorts

/-- The actual equality trace, including preserved external stacks and bounds
on the suffixes which the cleanup stage must consume. -/
theorem equality_eval (d : Data) :
    ∃ n ≤ 9 * ((d.stacks 1).length + 1), ∃ e : Data,
      Eval (.call equalityProgram) n d e ∧
      e.regs 4 = decide (d.stacks 1 = d.stacks 12) ∧
      (e.stacks 1).length ≤ (d.stacks 1).length ∧
      (e.stacks 12).length ≤ (d.stacks 12).length ∧
      (∀ j, j ≠ 1 → j ≠ 12 → e.stacks j = d.stacks j) := by
  obtain ⟨c, ⟨n, hn, ht⟩, hp, hout, hleft, hright⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded d.regs (d.stacks 1) (d.stacks 12)
  let a : StructuredProgram.State 5 2 :=
    ⟨d.regs, ExecClauseCost.bitStacks (d.stacks 1) (d.stacks 12)⟩
  let b : StructuredProgram.State 5 2 := ⟨c.regs, c.stacks⟩
  let e := embedState id equalityPorts d b
  have ha : embedState id equalityPorts d a = d := by
    apply embedState_eq _ _ Function.injective_id equalityPorts_injective
    · intro j; rfl
    · intro j; fin_cases j <;> simp [a, equalityPorts, ExecClauseCost.bitStacks]
    · intros; rfl
    · intros; rfl
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, StructuredProgram.State.withPC]
  have ht' : Trace ExecClauseCost.bitEqualityProgram n
      (a.withPC (some ExecClauseCost.bitEqualityProgram.entry)) (b.withPC none) := by
    rw [hcfg]
    exact ht
  have he := eval_call_lifted ExecClauseCost.bitEqualityProgram id equalityPorts d
    Function.injective_id equalityPorts_injective ht'
  refine ⟨n, hn, e, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ha, equalityProgram] using he
  · change (embedState id equalityPorts d b).regs (id 4) = _
    rw [embedState_register _ _ _ _ Function.injective_id]
    exact hout
  · change ((embedState id equalityPorts d b).stacks (equalityPorts 0)).length ≤ _
    rw [embedState_stack _ _ _ _ equalityPorts_injective]
    exact hleft
  · change ((embedState id equalityPorts d b).stacks (equalityPorts 1)).length ≤ _
    rw [embedState_stack _ _ _ _ equalityPorts_injective]
    exact hright
  · intro j hj1 hj12
    exact embedState_stack_frame _ _ _ _ j (by
      rintro ⟨i, hi⟩
      fin_cases i <;> simp_all [equalityPorts])

def afterClear (d : Data) (src : Fin 13) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

theorem clear_eval (d : Data) (src : Fin 13) :
    Eval (.call (clearProgram src (0 : Fin 5) 1))
      (2 * (d.stacks src).length + 3) d (afterClear d src) := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (0 : Fin 5) 1 d.regs d.stacks)
    2 rfl rfl
  simpa [afterClear, StructuredProgram.State.withPC, clearResult, clearProgram,
    Nat.add_assoc] using h

abbrev finishCommand : Cmd 5 13 :=
  .seq (.call (clearProgram (1 : Fin 13) (0 : Fin 5) 1))
    (.seq (.call (clearProgram (12 : Fin 13) (0 : Fin 5) 1))
      (.seq (.base (.atom (.push 11 4)))
        (.seq (.base (.atom (.set 2 false)))
          (.seq (.base (.atom (.set 3 false))) (.base (.atom (.set 4 false)))))))

def sealed (d : Data) (answer : Bool) : Data :=
  ⟨fun _ => false,
    Function.update (Function.update (Function.update d.stacks 1 []) 12 [])
      11 (answer :: d.stacks 11)⟩

theorem finish_eval (d : Data) :
    Eval finishCommand (2 * (d.stacks 1).length + 2 * (d.stacks 12).length + 10)
      d (sealed d (d.regs 4)) := by
  let d1 := afterClear d 1
  let d2 := afterClear d1 12
  let d3 := (StructuredProgram.Atom.push (11 : Fin 13) (4 : Fin 5)).eval d2
  let d4 := (StructuredProgram.Atom.set (2 : Fin 5) false).eval d3
  let d5 := (StructuredProgram.Atom.set (3 : Fin 5) false).eval d4
  let d6 := (StructuredProgram.Atom.set (4 : Fin 5) false).eval d5
  have hf : d6 = sealed d (d.regs 4) := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [d6, d5, d4, d3, d2, d1, afterClear, sealed, readRegs,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
    · funext j
      simp [d6, d5, d4, d3, d2, d1, afterClear, sealed, readRegs, clearStacks,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr]
  have he : Eval finishCommand
      ((2 * (d.stacks 1).length + 3) +
        ((2 * (d1.stacks 12).length + 3) + (1 + (1 + (1 + 1))))) d d6 :=
    .seq (clear_eval d 1) (.seq (clear_eval d1 12)
      (.seq (.base (.atom _ _)) (.seq (.base (.atom _ _))
        (.seq (.base (.atom _ _)) (.base (.atom _ _))))))
  rw [hf] at he
  convert he using 1
  simp [d1, afterClear, clearStacks]
  omega

abbrev sealCommand : Cmd 5 13 := .seq (.call equalityProgram) finishCommand

/-- Comparing, cleaning, and emitting is a fixed-code operation. Every stack
outside the two type buffers and the stream is preserved. -/
theorem seal_eval (d : Data) :
    ∃ n ≤ 11 * (d.stacks 1).length + 2 * (d.stacks 12).length + 19,
      Eval sealCommand n d (sealed d (decide (d.stacks 1 = d.stacks 12))) := by
  obtain ⟨n, hn, e, he, hout, hl, hr, hframe⟩ := equality_eval d
  have hf := finish_eval e
  have hseal : sealed e (e.regs 4) = sealed d (decide (d.stacks 1 = d.stacks 12)) := by
    apply state_ext
    · rfl
    · funext j
      by_cases h1 : j = 1
      · subst j; simp [sealed]
      by_cases h12 : j = 12
      · subst j; simp [sealed]
      by_cases h11 : j = 11
      · subst j; simp [sealed, hout, hframe 11 (by decide) (by decide)]
      · simp [sealed, h1, h12, h11, hframe j h1 h12]
  rw [hseal] at hf
  exact ⟨n + (2 * (e.stacks 1).length + 2 * (e.stacks 12).length + 10),
    by omega, he.seq hf⟩

def gatherRegs : Fin 3 → Fin 5 := Fin.castAdd 2

theorem gatherRegs_injective : Function.Injective gatherRegs := by
  intro a b h
  exact Fin.ext (congrArg (fun j : Fin 5 => j.val) h)

def leftPorts : Fin 10 → Fin 13 := Fin.castAdd 3

def rightPorts (i : Fin 10) : Fin 13 :=
  if i = 1 then 12 else if i = 8 then 10 else leftPorts i

theorem leftPorts_injective : Function.Injective leftPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun j : Fin 13 => j.val) h)

theorem rightPorts_injective : Function.Injective rightPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rightPorts, leftPorts]

abbrev leftGather : Cmd 5 13 :=
  .call (ProgramLinking.liftProgram GatherProgram.program gatherRegs leftPorts)

abbrev rightGather : Cmd 5 13 :=
  .call (ProgramLinking.liftProgram GatherProgram.program gatherRegs rightPorts)

/-- State at a callback boundary. The two plan arguments are serialized bytes;
after a gather its plan is consumed. Only the row table, width, and stream are
persistent at this boundary. -/
def stageState (rows : List (List Bool)) (width left right planLeft planRight stream : List Bool) :
    Data :=
  ⟨fun _ => false,
    fun j => if j = 0 then rows.flatten else if j = 3 then width
      else if j = 1 then left else if j = 12 then right
      else if j = 8 then planLeft else if j = 10 then planRight
      else if j = 11 then stream else []⟩

def planBytes (plan : List ℕ) : List Bool :=
  ProgramEncoding.encodeRecords (GatherProgram.indexRecords plan)

def inputState (rows : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (stream : List Bool) : Data :=
  stageState rows width [] [] (planBytes left) (planBytes right) stream

def outputState (rows : List (List Bool)) (width stream : List Bool) : Data :=
  stageState rows width [] [] [] [] stream

theorem leftGather_eval (rows : List (List Bool)) (width : List Bool)
    (plan : List ℕ) (rightPlan stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n ≤ GatherProgram.traceCost rows width.length plan,
    Eval leftGather n
      (stageState rows width [] [] (planBytes plan) rightPlan stream)
      (stageState rows width (GatherProgram.gathered rows plan) [] [] rightPlan stream) := by
  let d := stageState rows width [] [] (planBytes plan) rightPlan stream
  have ha : embedState gatherRegs leftPorts d (GatherProgram.inputState rows width plan) = d := by
    apply embedState_eq _ _ gatherRegs_injective leftPorts_injective
    · intro j; fin_cases j <;> simp [d, stageState, gatherRegs, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports]
    · intro j; fin_cases j <;> simp [d, stageState, leftPorts, planBytes,
        GatherProgram.inputState, GatherProgram.baseState, RecordPrograms.state,
        GatherProgram.ports]
    · intros; rfl
    · intros; rfl
  have hb : embedState gatherRegs leftPorts d (GatherProgram.outputState rows width plan) =
      stageState rows width (GatherProgram.gathered rows plan) [] [] rightPlan stream := by
    apply embedState_eq _ _ gatherRegs_injective leftPorts_injective
    · intro j; fin_cases j <;> simp [stageState, gatherRegs, GatherProgram.outputState]
    · intro j; fin_cases j <;> simp [stageState, leftPorts, GatherProgram.outputState]
    · intros; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [leftPorts] using h.symm⟩
      have h8 : j ≠ 8 := fun h => hj ⟨8, by simpa [leftPorts] using h.symm⟩
      simp [d, stageState, h1, h8]
  obtain ⟨n, hn, ht⟩ := GatherProgram.program_run rows width plan hrows hplan
  have he := eval_call_lifted GatherProgram.program gatherRegs leftPorts d
    gatherRegs_injective leftPorts_injective ht
  exact ⟨n, hn, by simpa only [ha, hb, leftGather] using he⟩

theorem rightGather_eval (rows : List (List Bool)) (width left stream : List Bool)
    (plan : List ℕ) (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n ≤ GatherProgram.traceCost rows width.length plan,
    Eval rightGather n
      (stageState rows width left [] [] (planBytes plan) stream)
      (stageState rows width left (GatherProgram.gathered rows plan) [] [] stream) := by
  let d := stageState rows width left [] [] (planBytes plan) stream
  have ha : embedState gatherRegs rightPorts d (GatherProgram.inputState rows width plan) = d := by
    apply embedState_eq _ _ gatherRegs_injective rightPorts_injective
    · intro j; fin_cases j <;> simp [d, stageState, gatherRegs, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports]
    · intro j; fin_cases j <;> simp [d, stageState, rightPorts, leftPorts, planBytes,
        GatherProgram.inputState, GatherProgram.baseState, RecordPrograms.state,
        GatherProgram.ports]
    · intros; rfl
    · intros; rfl
  have hb : embedState gatherRegs rightPorts d (GatherProgram.outputState rows width plan) =
      stageState rows width left (GatherProgram.gathered rows plan) [] [] stream := by
    apply embedState_eq _ _ gatherRegs_injective rightPorts_injective
    · intro j; fin_cases j <;> simp [stageState, gatherRegs, GatherProgram.outputState]
    · intro j; fin_cases j <;> simp [stageState, rightPorts, leftPorts, GatherProgram.outputState]
    · intros; rfl
    · intro j hj
      have h12 : j ≠ 12 := fun h => hj ⟨1, by simpa [rightPorts] using h.symm⟩
      have h10 : j ≠ 10 := fun h => hj ⟨8, by simpa [rightPorts] using h.symm⟩
      simp [d, stageState, h12, h10]
  obtain ⟨n, hn, ht⟩ := GatherProgram.program_run rows width plan hrows hplan
  have he := eval_call_lifted GatherProgram.program gatherRegs rightPorts d
    gatherRegs_injective rightPorts_injective ht
  exact ⟨n, hn, by simpa only [ha, hb, rightGather] using he⟩

abbrev command : Cmd 5 13 := .seq leftGather (.seq rightGather sealCommand)

abbrev program : Program 5 13 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 11

def collisionBit (rows : List (List Bool)) (left right : List ℕ) : Bool :=
  decide (GatherProgram.gathered rows left = GatherProgram.gathered rows right)

def sourceBudget (rows : List (List Bool)) (width : ℕ) (left right : List ℕ) : ℕ :=
  GatherProgram.traceCost rows width left + GatherProgram.traceCost rows width right +
    11 * (GatherProgram.gathered rows left).length +
    2 * (GatherProgram.gathered rows right).length + 20

/-- The source bound can be read from the unary plans and word width alone;
the table contents do not affect it. -/
def planBudget (width : ℕ) (left right : List ℕ) : ℕ :=
  34 + (14 * width + 16) * (left.sum + right.sum) +
    (32 * width + 27) * left.length + (23 * width + 27) * right.length

theorem sourceBudget_eq_planBudget (rows : List (List Bool)) (width : ℕ)
    (left right : List ℕ) (hrows : ∀ row ∈ rows, row.length = width)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    sourceBudget rows width left right = planBudget width left right := by
  rw [sourceBudget, GatherProgram.traceCost, GatherProgram.traceCost,
    GatherProgram.iterator_budget_eq, GatherProgram.iterator_budget_eq,
    GatherProgram.gathered_length rows left width hrows hleft,
    GatherProgram.gathered_length rows right width hrows hright]
  unfold planBudget
  ring

theorem callback_eval (rows : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    ∃ n, n + 1 ≤ sourceBudget rows width.length left right ∧
      Eval command n (inputState rows width left right stream)
        (outputState rows width (collisionBit rows left right :: stream)) := by
  obtain ⟨nl, hnl, hl⟩ := leftGather_eval rows width left (planBytes right) stream hrows hleft
  obtain ⟨nr, hnr, hr⟩ := rightGather_eval rows width
    (GatherProgram.gathered rows left) stream right hrows hright
  let d := stageState rows width (GatherProgram.gathered rows left)
    (GatherProgram.gathered rows right) [] [] stream
  obtain ⟨n, hn, hs⟩ := seal_eval d
  have hd : sealed d (decide (d.stacks 1 = d.stacks 12)) =
      outputState rows width (collisionBit rows left right :: stream) := by
    apply state_ext
    · rfl
    · funext j
      fin_cases j <;> simp [d, stageState, sealed, outputState, collisionBit]
  rw [hd] at hs
  refine ⟨nl + (nr + n), ?_, hl.seq (hr.seq hs)⟩
  simp [d, stageState] at hn
  simp only [sourceBudget]
  omega

/-- One actual fixed-program run gathers both types, emits their collision bit,
and restores the scratch stacks and registers for the next callback. -/
theorem program_trace (rows : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    ∃ n ≤ sourceBudget rows width.length left right,
      Trace program n
        ((inputState rows width left right stream).withPC (some program.entry))
        ((outputState rows width (collisionBit rows left right :: stream)).withPC none) := by
  obtain ⟨n, hn, he⟩ := callback_eval rows width left right stream hrows hleft hright
  exact ⟨n + 1, hn, compiled_halt_trace he 0 11⟩

/-- The primitive compiler sees the streamed bit on the designated output stack. -/
theorem primitive_runs (rows : List (List Bool)) (width : List Bool)
    (left right : List ℕ) (stream : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    ∃ c : (primitive program).Cfg,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * sourceBudget rows width.length left right)
        (primitiveCfg program
          ((inputState rows width left right stream).withPC (some program.entry))) c ∧
      c.state = .inl (collisionBit rows left right) := by
  obtain ⟨n, hn, ht⟩ := program_trace rows width left right stream hrows hleft hright
  let c : Cfg 5 13 (StructuredCalls.size command + 1) :=
    (outputState rows width (collisionBit rows left right :: stream)).withPC none
  refine ⟨primitiveCfg program c, BitProgram.primitive_execution program ⟨n, hn, ht⟩, ?_⟩
  rw [primitive_halted program c rfl]
  simp [c, outputState, stageState, program, StructuredCalls.compiled
    ]

theorem sourceBudget_le (rows : List (List Bool)) (width : ℕ) (left right : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width)
    (hleft : ∀ i ∈ left, i < rows.length) (hright : ∀ i ∈ right, i < rows.length) :
    sourceBudget rows width left right ≤
      34 + (left.length + right.length) *
        (rows.length * (14 * width + 16) + 32 * width + 27) := by
  have hl := GatherProgram.traceCost_le rows width left hrows hleft
  have hr := GatherProgram.traceCost_le rows width right hrows hright
  rw [sourceBudget, GatherProgram.gathered_length rows left width hrows hleft,
    GatherProgram.gathered_length rows right width hrows hright]
  nlinarith

section Assignments

open MulticolorTypes SubexpTypeVariance SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]
variable {r Q Δ : ℕ} (P : Factor.Pattern V E) (slots : SlotMap P Δ)

/-- ReadPlan's word-array refinement applies to the bytes actually gathered by
the fixed machine, including head/slot order and one-hot color encoding. -/
theorem gathered_assignmentType (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (ω : Assignment V E r Q Δ) (v : V) :
    GatherProgram.gathered (ReadPlan.seedRows vertices factors ω)
      (ReadPlan.vertexPlan P slots vertices factors v) =
        CollisionProgram.encodeType (assignmentType P slots ω v) :=
  ReadPlan.gather_seedRows P slots vertices factors hv he ω v

theorem collisionBit_assignment (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (ω : Assignment V E r Q Δ) (pair : V × V) :
    collisionBit (ReadPlan.seedRows vertices factors ω)
      (ReadPlan.vertexPlan P slots vertices factors pair.1)
      (ReadPlan.vertexPlan P slots vertices factors pair.2) =
        decide (LocalExpectation.naturalPairTerm P slots pair ω = 1) := by
  unfold collisionBit
  rw [gathered_assignmentType P slots vertices factors hv he ω pair.1,
    gathered_assignmentType P slots vertices factors hv he ω pair.2]
  by_cases h : assignmentType P slots ω pair.1 = assignmentType P slots ω pair.2
  · simp [h, LocalExpectation.naturalPairTerm]
  · simp [h, LocalExpectation.naturalPairTerm]

/-- An actual primitive execution computes the collision leaf from the packed
seed rows and two runtime read plans. Encoding the whole type is done by the
two gather programs during this trace. -/
theorem assigned_primitive_runs (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (ω : Assignment V E r Q Δ) (pair : V × V) (stream : List Bool) :
    ∃ c : (primitive program).Cfg,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          sourceBudget (ReadPlan.seedRows vertices factors ω) (ReadPlan.wordWidth r Q)
            (ReadPlan.vertexPlan P slots vertices factors pair.1)
            (ReadPlan.vertexPlan P slots vertices factors pair.2))
        (primitiveCfg program
          ((inputState (ReadPlan.seedRows vertices factors ω)
            (List.replicate (ReadPlan.wordWidth r Q) true)
            (ReadPlan.vertexPlan P slots vertices factors pair.1)
            (ReadPlan.vertexPlan P slots vertices factors pair.2) stream).withPC
              (some program.entry))) c ∧
      c.state = .inl (decide (LocalExpectation.naturalPairTerm P slots pair ω = 1)) := by
  have hwidth : ∀ row ∈ ReadPlan.seedRows vertices factors ω,
      row.length = (List.replicate (ReadPlan.wordWidth r Q) true).length := by
    intro row hrow
    simpa using ReadPlan.seedRows_width vertices factors ω row hrow
  have hvalid (v : V) : ∀ i ∈ ReadPlan.vertexPlan P slots vertices factors v,
      i < (ReadPlan.seedRows vertices factors ω).length := by
    intro i hi
    simpa [ReadPlan.seedRows, ReadPlan.seedWords] using
      ReadPlan.vertexPlan_valid P slots vertices factors hv he v i hi
  obtain ⟨c, hc, hout⟩ := primitive_runs (ReadPlan.seedRows vertices factors ω)
    (List.replicate (ReadPlan.wordWidth r Q) true)
    (ReadPlan.vertexPlan P slots vertices factors pair.1)
    (ReadPlan.vertexPlan P slots vertices factors pair.2) stream hwidth
    (hvalid pair.1) (hvalid pair.2)
  refine ⟨c, by simpa using hc, ?_⟩
  rw [collisionBit_assignment P slots vertices factors hv he ω pair] at hout
  exact hout

def completionRows (current candidate : List (Word r Q)) : List (List Bool) :=
  (current ++ candidate).map ReadPlan.encodeWord

def completionPlan (vertices : List V) (factors : List E) (currentSize : ℕ)
    (remaining : List ℕ) (v : V) : List ℕ :=
  ReadPlan.completionPlan currentSize remaining (ReadPlan.vertexPlan P slots vertices factors v)

theorem completionRows_width (current candidate : List (Word r Q))
    (row : List Bool) (hrow : row ∈ completionRows current candidate) :
    row.length = ReadPlan.wordWidth r Q := by
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hrow
  exact ReadPlan.encodeWord_length w

theorem completionPlan_valid (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (current candidate : List (Word r Q)) (remaining : List ℕ)
    (hc : (AssignmentEnumeration.seedIndices vertices factors Δ).length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (v : V) :
    ∀ i ∈ completionPlan P slots vertices factors current.length remaining v,
      i < (completionRows current candidate).length := by
  intro i hi
  have hp : ∀ j ∈ ReadPlan.vertexPlan P slots vertices factors v, j < current.length :=
    fun j hj => (ReadPlan.vertexPlan_valid P slots vertices factors hv he v j hj).trans_le hc
  simpa [completionRows] using
    ReadPlan.completionPlan_valid current.length candidate.length remaining
      (ReadPlan.vertexPlan P slots vertices factors v) hr hp i hi

theorem collisionBit_completed (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (current candidate : List (Word r Q)) (remaining : List ℕ)
    (hc : (AssignmentEnumeration.seedIndices vertices factors Δ).length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (pair : V × V) :
    collisionBit (completionRows current candidate)
      (completionPlan P slots vertices factors current.length remaining pair.1)
      (completionPlan P slots vertices factors current.length remaining pair.2) =
        decide (LocalExpectation.naturalPairTerm P slots pair
          (ReadPlan.completedAssignment vertices factors default current remaining candidate) = 1) := by
  change decide (ReadPlan.partialEncoding P slots vertices factors current remaining candidate pair.1 =
    ReadPlan.partialEncoding P slots vertices factors current remaining candidate pair.2) = _
  rw [ReadPlan.partialEncoding_eq P slots vertices factors hv he default current remaining candidate hc hr,
    ReadPlan.partialEncoding_eq P slots vertices factors hv he default current remaining candidate hc hr]
  by_cases h : assignmentType P slots
      (ReadPlan.completedAssignment vertices factors default current remaining candidate) pair.1 =
      assignmentType P slots
        (ReadPlan.completedAssignment vertices factors default current remaining candidate) pair.2
  · simp [h, LocalExpectation.naturalPairTerm]
  · simp [h, LocalExpectation.naturalPairTerm]

/-- Runtime-selected reads from the current-array/candidate-tuple table compute
the completed assignment's collision leaf. Selection indices and the table are
explicit input data; no function-valued callback is supplied to the program. -/
theorem completed_primitive_runs (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (current candidate : List (Word r Q)) (remaining : List ℕ)
    (hc : (AssignmentEnumeration.seedIndices vertices factors Δ).length ≤ current.length)
    (hr : remaining.length ≤ candidate.length) (pair : V × V) (stream : List Bool) :
    ∃ c : (primitive program).Cfg,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          sourceBudget (completionRows current candidate) (ReadPlan.wordWidth r Q)
            (completionPlan P slots vertices factors current.length remaining pair.1)
            (completionPlan P slots vertices factors current.length remaining pair.2))
        (primitiveCfg program
          ((inputState (completionRows current candidate)
            (List.replicate (ReadPlan.wordWidth r Q) true)
            (completionPlan P slots vertices factors current.length remaining pair.1)
            (completionPlan P slots vertices factors current.length remaining pair.2)
            stream).withPC (some program.entry))) c ∧
      c.state = .inl (decide (LocalExpectation.naturalPairTerm P slots pair
        (ReadPlan.completedAssignment vertices factors default current remaining candidate) = 1)) := by
  have hwidth : ∀ row ∈ completionRows current candidate,
      row.length = (List.replicate (ReadPlan.wordWidth r Q) true).length := by
    intro row hrow
    simpa using completionRows_width current candidate row hrow
  obtain ⟨c, ht, hout⟩ := primitive_runs (completionRows current candidate)
    (List.replicate (ReadPlan.wordWidth r Q) true)
    (completionPlan P slots vertices factors current.length remaining pair.1)
    (completionPlan P slots vertices factors current.length remaining pair.2) stream hwidth
    (completionPlan_valid P slots vertices factors hv he current candidate remaining hc hr pair.1)
    (completionPlan_valid P slots vertices factors hv he current candidate remaining hc hr pair.2)
  refine ⟨c, by simpa using ht, ?_⟩
  rw [collisionBit_completed P slots vertices factors hv he default current candidate remaining hc hr pair]
    at hout
  exact hout

/-- Specialization to the exact optional-update assignment at a padded tuple
leaf. Dummy tuple coordinates do not change its selected words. -/
theorem leaf_primitive_runs (vertices : List V) (factors : List E)
    (hv : ∀ v, v ∈ vertices) (he : ∀ e, e ∈ factors)
    (default : Word r Q) (fixed candidate : List (Word r Q)) (remaining : List ℕ)
    (hn : remaining.Nodup) (hr : remaining.length ≤ candidate.length)
    (S : ℕ) (pair : V × V) (stream : List Bool) :
    let current := ReadPlan.currentArray default
      (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed
    ∃ c : (primitive program).Cfg,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program *
          sourceBudget (completionRows current candidate) (ReadPlan.wordWidth r Q)
            (completionPlan P slots vertices factors current.length remaining pair.1)
            (completionPlan P slots vertices factors current.length remaining pair.2))
        (primitiveCfg program
          ((inputState (completionRows current candidate)
            (List.replicate (ReadPlan.wordWidth r Q) true)
            (completionPlan P slots vertices factors current.length remaining pair.1)
            (completionPlan P slots vertices factors current.length remaining pair.2)
            stream).withPC (some program.entry))) c ∧
      c.state = .inl (decide (LocalExpectation.naturalPairTerm P slots pair
        (ReadPlan.leafAssignment vertices factors default fixed remaining candidate S) = 1)) := by
  dsimp only
  have h := completed_primitive_runs P slots vertices factors hv he default
    (ReadPlan.currentArray default (AssignmentEnumeration.seedIndices vertices factors Δ).length fixed)
    candidate remaining (by simp) hr pair stream
  rw [ReadPlan.completedAssignment_eq_leaf vertices factors hv he default fixed remaining candidate S hn hr]
    at h
  exact h

end Assignments

end SubexponentialSAT.Subexp.CollisionStreamProgram

end OAI.Algorithms
