import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionGenerateProgram

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

open BitProgram StackRoutines StructuredCalls

abbrev Data := StructuredProgram.State 13 26
abbrev PlanPair := List ℕ × List ℕ

/-- Public pair-record payload: exactly two consecutive escape frames, each
containing the selected plan's ordinary unary-index record encoding. -/
def pairBytes (pair : PlanPair) : List Bool :=
  Encoding.frame (CollisionStreamProgram.planBytes pair.1) ++
    Encoding.frame (CollisionStreamProgram.planBytes pair.2)

/-- Runtime list framing around the public pair payloads. -/
def pairRecords (pairs : List PlanPair) : List Bool :=
  ProgramEncoding.encodeRecords (pairs.map pairBytes)

def readPlan (bits : List Bool) : List ℕ :=
  ((ProgramEncoding.readRecords bits).map (fun p => p.1.map List.length)).getD []

def readPair (bits : List Bool) : PlanPair :=
  ((do
    let (left, rest) ← Encoding.readFrame bits
    let (right, _) ← Encoding.readFrame rest
    pure (readPlan left, readPlan right)) : Option PlanPair).getD ([], [])

@[simp] theorem readPlan_planBytes (plan : List ℕ) :
    readPlan (CollisionStreamProgram.planBytes plan) = plan := by
  simp [readPlan, CollisionStreamProgram.planBytes, GatherProgram.indexRecords,
    List.map_map, Function.comp_def]

@[simp] theorem readPair_pairBytes (pair : PlanPair) : readPair (pairBytes pair) = pair := by
  rcases pair with ⟨left, right⟩
  have hr : Encoding.readFrame (Encoding.frame (CollisionStreamProgram.planBytes right)) =
      some (CollisionStreamProgram.planBytes right, []) := by
    simpa only [List.append_nil] using
      Encoding.readFrame_frame_append (CollisionStreamProgram.planBytes right) []
  simp [readPair, pairBytes, hr]

structure Context where
  current : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)
  depth : List Bool

def Context.Valid (ctx : Context) : Prop :=
  (∀ row ∈ ctx.current, row.length = ctx.width.length) ∧
    (∀ row ∈ ctx.alphabet, row.length = ctx.width.length)

def ValidPair (ctx : Context) (pair : PlanPair) : Prop :=
  (∀ i ∈ pair.1, i < ctx.current.length + ctx.depth.length) ∧
    (∀ i ∈ pair.2, i < ctx.current.length + ctx.depth.length)

def ports : RecordPrograms.Ports 13 26 where
  tag := 10
  present := 11
  found := 12
  source := 20
  payload := 21
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def fieldPorts : RecordPrograms.Ports 13 26 where
  tag := 0
  present := 1
  found := 2
  source := 22
  payload := 25
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

/-- Persistent ports are current 13, width 3, alphabet 19, depth template 23.
Stream 11 accumulates leaves; stack 18 is reserved for the final unary score. -/
def baseState (ctx : Context) (stream : List Bool) : Data :=
  ⟨fun j => decide (j = 11), fun j =>
    if j = 3 then ctx.width else if j = 13 then ctx.current.flatten
    else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
    else if j = 23 then ctx.depth else if j = 11 then stream else []⟩

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

def transferred (src dst : Fin 26) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

abbrev transfer (src dst : Fin 26) : Cmd 13 26 :=
  .call (transferProgram src dst 0 1)

theorem transfer_eval (src dst : Fin 26) (hne : src ≠ dst) (d : Data) :
    Eval (transfer src dst) (3 * (d.stacks src).length + 3) d (transferred src dst d) := by
  apply Eval.call
  simpa [transfer, transferred, transferProgram, transferResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using
    halt_after_trace _ (transferProgram_trace src dst (0 : Fin 13) 1 hne (by decide)
      d.regs d.stacks) 3 rfl rfl

def cleared (src : Fin 26) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, clearStacks src d.stacks⟩

abbrev clear (src : Fin 26) : Cmd 13 26 := .call (clearProgram src 0 1)

theorem clear_eval (src : Fin 26) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared src d) := by
  apply Eval.call
  simpa [clear, cleared, clearProgram, clearResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using
    halt_after_trace _ (clearProgram_trace src (0 : Fin 13) 1 d.regs d.stacks) 2 rfl rfl

def copiedDepth (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks (23 : Fin 26) 17 d.stacks⟩

abbrev copyDepth : Cmd 13 26 := .call (copyProgram 23 17 24 0 1)

theorem copyDepth_eval (d : Data) (htmp : d.stacks 24 = []) :
    Eval copyDepth (7 * (d.stacks 23).length + 5) d (copiedDepth d) := by
  apply Eval.call
  simpa [copyDepth, copiedDepth, copyProgram, copyResult,
    StructuredProgram.State.withPC, Nat.add_assoc] using
    halt_after_trace _ (copyProgram_trace (23 : Fin 26) 17 24 (0 : Fin 13) 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks htmp) 7 rfl rfl

def fieldRead (bits tail : List Bool) (d : Data) : Data :=
  RecordPrograms.state fieldPorts d false true (d.regs 2) tail (bits.reverse ++ d.stacks 25)

theorem readField_eval (d : Data) (bits tail : List Bool)
    (hsrc : d.stacks 22 = Encoding.frame bits ++ tail) :
    Eval (RecordPrograms.reader fieldPorts) (6 * bits.length + 4) d (fieldRead bits tail d) := by
  have h := RecordPrograms.reader_eval fieldPorts d bits tail (d.stacks 25)
    (d.regs 0) (d.regs 1) (d.regs 2)
  have hd : RecordPrograms.state fieldPorts d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) (d.stacks 25) = d :=
    RecordPrograms.state_eq_self fieldPorts d _ _ _ _ _ rfl rfl rfl hsrc rfl
  simpa only [hd, fieldRead] using h

def resetList : List (Fin 13) → StructuredProgram.Cmd 13 26
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

def resetValues (indices : List (Fin 13)) (regs : Fin 13 → Bool) : Fin 13 → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

theorem resetList_eval (indices : List (Fin 13)) (d : Data) :
    StructuredProgram.Eval (resetList indices) indices.length d
      ⟨resetValues indices d.regs, d.stacks⟩ := by
  induction indices generalizing d with
  | nil => exact .skip d
  | cons i rest ih =>
    have h := (StructuredProgram.Eval.atom (.set i false) d).seq
      (ih ((StructuredProgram.Atom.set i false).eval d))
    simpa [resetList, resetValues, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC, execInstr, Nat.add_comm] using h

abbrev resetInner : Cmd 13 26 := .base (resetList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

def resetInnerAfter (d : Data) : Data :=
  ⟨fun j => if j.val < 10 then false else d.regs j, d.stacks⟩

theorem resetInner_eval (d : Data) : Eval resetInner 10 d (resetInnerAfter d) := by
  have he := resetList_eval [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] d
  have hr : resetValues [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] d.regs =
      fun j => if j.val < 10 then false else d.regs j := by
    funext j
    fin_cases j <;> simp [resetValues]
  rw [hr] at he
  simpa [resetInner, resetInnerAfter] using Eval.base he

private theorem embedState_eq {r s R S : ℕ}
    (reg : Fin r → Fin R) (stack : Fin s → Fin S)
    (hreg : Function.Injective reg) (hstack : Function.Injective stack)
    (frame target : StructuredProgram.State R S) (source : StructuredProgram.State r s)
    (hr : ∀ i, target.regs (reg i) = source.regs i)
    (hs : ∀ i, target.stacks (stack i) = source.stacks i)
    (hfr : ∀ j, (¬ ∃ i, reg i = j) → target.regs j = frame.regs j)
    (hfs : ∀ j, (¬ ∃ i, stack i = j) → target.stacks j = frame.stacks j) :
    embedState reg stack frame source = target := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    change (embedState reg stack frame source).regs j = target.regs j
    by_cases hj : ∃ i, reg i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_register reg stack frame source hreg]
      exact (hr i).symm
    · rw [embedState_register_frame reg stack frame source j hj]
      exact (hfr j hj).symm
  · funext j
    change (embedState reg stack frame source).stacks j = target.stacks j
    by_cases hj : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack reg stack frame source hstack]
      exact (hs i).symm
    · rw [embedState_stack_frame reg stack frame source j hj]
      exact (hfs j hj).symm

def generatorRegs : Fin 10 → Fin 13 := Fin.castAdd 3
def generatorPorts : Fin 20 → Fin 26 := Fin.castAdd 6

theorem generatorRegs_injective : Function.Injective generatorRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 13 => k.val) h)

theorem generatorPorts_injective : Function.Injective generatorPorts := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 26 => k.val) h)

abbrev generate : Cmd 13 26 :=
  .call (ProgramLinking.liftProgram CollisionGenerateProgram.program generatorRegs generatorPorts)

def pairPrepared (ctx : Context) (tail stream : List Bool) (pair : PlanPair) : Data :=
  let d := RecordPrograms.state ports (baseState ctx stream) false true false tail []
  ⟨d.regs, Function.update (Function.update (Function.update d.stacks
      14 (CollisionStreamProgram.planBytes pair.1))
      15 (CollisionStreamProgram.planBytes pair.2)) 17 ctx.depth⟩

def pairStream (ctx : Context) (pair : PlanPair) (stream : List Bool) : List Bool :=
  CollisionTupleProgram.streamed ctx.current.flatten ctx.width.length pair.1 pair.2
    (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]]) stream

def pairFinished (ctx : Context) (tail stream : List Bool) (pair : PlanPair) : Data :=
  let d := RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
    false true false tail []
  ⟨fun j => if j = 6 then true else d.regs j,
    Function.update (Function.update d.stacks 14 (CollisionStreamProgram.planBytes pair.1))
      15 (CollisionStreamProgram.planBytes pair.2)⟩

def generateCost (ctx : Context) (pair : PlanPair) : ℕ :=
  CollisionGenerateProgram.sourceBudget ctx.current.flatten ctx.width.length
    pair.1 pair.2 ctx.alphabet ctx.depth.length

/-- The actual generator is lifted into the aggregate scorer. Only the
separate parser/depth-template ports lie outside its footprint. -/
theorem generate_eval (ctx : Context) (hc : ctx.Valid) (pair : PlanPair)
    (hp : ValidPair ctx pair) (tail stream : List Bool) :
    ∃ n ≤ generateCost ctx pair, Eval generate n
      (pairPrepared ctx tail stream pair) (pairFinished ctx tail stream pair) := by
  obtain ⟨n, hn, ht⟩ := CollisionGenerateProgram.program_run_uniform
    ctx.current ctx.width pair.1 pair.2 ctx.alphabet ctx.depth stream hc.1 hc.2 hp.1 hp.2
  let d := pairPrepared ctx tail stream pair
  have hin : embedState generatorRegs generatorPorts d
      (CollisionGenerateProgram.inputState ctx.current.flatten ctx.width pair.1 pair.2
        ctx.alphabet ctx.depth stream) = d := by
    apply embedState_eq _ _ generatorRegs_injective generatorPorts_injective
    · intro i; fin_cases i <;>
        simp [d, pairPrepared, RecordPrograms.state, ports, baseState, generatorRegs,
          CollisionGenerateProgram.inputState, CollisionGenerateProgram.storedState]
    · intro i; fin_cases i <;>
        simp [d, pairPrepared, RecordPrograms.state, ports, baseState, generatorPorts,
          CollisionGenerateProgram.inputState, CollisionGenerateProgram.storedState]
    · intros; rfl
    · intros; rfl
  have hout : embedState generatorRegs generatorPorts d
      (CollisionGenerateProgram.outputState ctx.current.flatten ctx.width pair.1 pair.2
        (ProgramEncoding.encodeRecords ctx.alphabet) (pairStream ctx pair stream)) =
      pairFinished ctx tail stream pair := by
    apply embedState_eq _ _ generatorRegs_injective generatorPorts_injective
    · intro i; fin_cases i <;>
        simp [pairFinished, RecordPrograms.state, ports, baseState, generatorRegs,
          CollisionGenerateProgram.outputState, CollisionGenerateProgram.storedState]
    · intro i; fin_cases i <;>
        simp [pairFinished, RecordPrograms.state, ports, baseState, generatorPorts,
          CollisionGenerateProgram.outputState, CollisionGenerateProgram.storedState]
    · intro j hj
      have h6 : j ≠ 6 := fun h => hj ⟨6, by simpa [generatorRegs] using h.symm⟩
      simp [pairFinished, d, pairPrepared, h6, RecordPrograms.state, ports, baseState]
    · intro j hj
      have h11 : j ≠ 11 := fun h => hj ⟨11, by simpa [generatorPorts] using h.symm⟩
      have h17 : j ≠ 17 := fun h => hj ⟨17, by simpa [generatorPorts] using h.symm⟩
      simp [pairFinished, d, pairPrepared, RecordPrograms.state, ports, baseState,
        Function.update_apply, h11, h17]
  have he := eval_call_lifted CollisionGenerateProgram.program generatorRegs generatorPorts d
    generatorRegs_injective generatorPorts_injective ht
  dsimp only [pairStream] at hout
  exact ⟨n, hn, by simpa only [hin, hout, generate] using he⟩

abbrev prepare : Cmd 13 26 :=
  .seq (transfer 21 22) (.seq (RecordPrograms.reader fieldPorts)
    (.seq (transfer 25 14) (.seq (RecordPrograms.reader fieldPorts)
      (.seq (transfer 25 15) (.seq copyDepth resetInner)))))

def prepareCost (ctx : Context) (pair : PlanPair) : ℕ :=
  3 * (pairBytes pair).length +
    9 * ((CollisionStreamProgram.planBytes pair.1).length +
      (CollisionStreamProgram.planBytes pair.2).length) + 7 * ctx.depth.length + 32

theorem prepare_eval (ctx : Context) (pair : PlanPair) (tail stream : List Bool) :
    Eval prepare (prepareCost ctx pair)
      (RecordPrograms.state ports (baseState ctx stream)
        false true false tail (pairBytes pair).reverse)
      (pairPrepared ctx tail stream pair) := by
  let left := CollisionStreamProgram.planBytes pair.1
  let right := CollisionStreamProgram.planBytes pair.2
  let d0 := RecordPrograms.state ports (baseState ctx stream)
    false true false tail (pairBytes pair).reverse
  let d1 := transferred 21 22 d0
  let d2 := fieldRead left (Encoding.frame right) d1
  let d3 := transferred 25 14 d2
  let d4 := fieldRead right [] d3
  let d5 := transferred 25 15 d4
  let d6 := copiedDepth d5
  have h1 : Eval (transfer 21 22) (3 * (pairBytes pair).length + 3) d0 d1 := by
    simpa [d0, d1, RecordPrograms.state, ports] using
      transfer_eval 21 22 (by decide) d0
  have hs1 : d1.stacks 22 = Encoding.frame left ++ Encoding.frame right := by
    simp [d1, transferred, transferStacks, d0, RecordPrograms.state, ports,
      baseState, pairBytes, left, right]
  have h2 : Eval (RecordPrograms.reader fieldPorts) (6 * left.length + 4) d1 d2 :=
    readField_eval d1 left (Encoding.frame right) hs1
  have ho1 : d1.stacks 25 = [] := by
    simp [d1, transferred, transferStacks, d0, RecordPrograms.state, ports, baseState]
  have h3 : Eval (transfer 25 14) (3 * left.length + 3) d2 d3 := by
    simpa [d3, d2, fieldRead, RecordPrograms.state, fieldPorts, ho1] using
      transfer_eval 25 14 (by decide) d2
  have hs3 : d3.stacks 22 = Encoding.frame right ++ [] := by
    simp [d3, transferred, transferStacks, d2, fieldRead, RecordPrograms.state, fieldPorts]
  have h4 : Eval (RecordPrograms.reader fieldPorts) (6 * right.length + 4) d3 d4 :=
    readField_eval d3 right [] hs3
  have h5 : Eval (transfer 25 15) (3 * right.length + 3) d4 d5 := by
    simpa [d5, d4, fieldRead, RecordPrograms.state, fieldPorts, d3,
      transferred, transferStacks] using transfer_eval 25 15 (by decide) d4
  have ht : d5.stacks 24 = [] := by
    simp [d5, d4, d3, d2, d1, d0, transferred, transferStacks, fieldRead,
      RecordPrograms.state, fieldPorts, ports, baseState]
  have hd : d5.stacks 23 = ctx.depth := by
    simp [d5, d4, d3, d2, d1, d0, transferred, transferStacks, fieldRead,
      RecordPrograms.state, fieldPorts, ports, baseState]
  have h6 : Eval copyDepth (7 * ctx.depth.length + 5) d5 d6 := by
    simpa only [d6, hd] using copyDepth_eval d5 ht
  have hend : resetInnerAfter d6 = pairPrepared ctx tail stream pair := by
    apply state_ext
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d6, copiedDepth, d5, d4, d3, d2, d1, d0,
          transferred, fieldRead, RecordPrograms.state, fieldPorts, ports,
          baseState, pairPrepared, readRegs]
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d6, copiedDepth, copyStacks, d5, d4, d3, d2, d1, d0,
          transferred, transferStacks, fieldRead, RecordPrograms.state, fieldPorts, ports,
          baseState, pairPrepared, pairBytes, left, right]
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (resetInner_eval d6))))))
  rw [hend] at he
  convert he using 1 ; dsimp [prepare, prepareCost, left, right] ; ring

abbrev cleanup : Cmd 13 26 := .seq (clear 14) (.seq (clear 15) resetInner)

def cleanupCost (pair : PlanPair) : ℕ :=
  2 * ((CollisionStreamProgram.planBytes pair.1).length +
    (CollisionStreamProgram.planBytes pair.2).length) + 16

theorem cleanup_eval (ctx : Context) (pair : PlanPair) (tail stream : List Bool) :
    Eval cleanup (cleanupCost pair) (pairFinished ctx tail stream pair)
      (RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
        false true false tail []) := by
  let d0 := pairFinished ctx tail stream pair
  let d1 := cleared 14 d0
  let d2 := cleared 15 d1
  have h1 : Eval (clear 14) (2 * (CollisionStreamProgram.planBytes pair.1).length + 3)
      d0 d1 := by simpa [d0, d1, pairFinished] using clear_eval 14 d0
  have h2 : Eval (clear 15) (2 * (CollisionStreamProgram.planBytes pair.2).length + 3)
      d1 d2 := by
    simpa [d2, d1, cleared, clearStacks, d0, pairFinished] using clear_eval 15 d1
  have hend : resetInnerAfter d2 =
      RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
        false true false tail [] := by
    apply state_ext
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d2, d1, d0, cleared, pairFinished, readRegs,
          RecordPrograms.state, ports, baseState]
    · funext j; fin_cases j <;>
        simp [resetInnerAfter, d2, d1, d0, cleared, clearStacks, pairFinished,
          RecordPrograms.state, ports, baseState]
  have he := h1.seq (h2.seq (resetInner_eval d2))
  rw [hend] at he
  convert he using 1 ; dsimp [cleanup, cleanupCost] ; ring

abbrev callback : Cmd 13 26 := .seq prepare (.seq generate cleanup)

def callbackCost (ctx : Context) (bits : List Bool) : ℕ :=
  prepareCost ctx (readPair bits) + generateCost ctx (readPair bits) +
    cleanupCost (readPair bits)

theorem callback_eval (ctx : Context) (hc : ctx.Valid) (pair : PlanPair)
    (hp : ValidPair ctx pair) (tail stream : List Bool) :
    ∃ n ≤ callbackCost ctx (pairBytes pair), Eval callback n
      (RecordPrograms.state ports (baseState ctx stream)
        false true false tail (pairBytes pair).reverse)
      (RecordPrograms.state ports (baseState ctx (pairStream ctx pair stream))
        false true false tail []) := by
  obtain ⟨n, hn, he⟩ := generate_eval ctx hc pair hp tail stream
  refine ⟨prepareCost ctx pair + (n + cleanupCost pair), ?_,
    (prepare_eval ctx pair tail stream).seq (he.seq (cleanup_eval ctx pair tail stream))⟩
  simpa only [callbackCost, readPair_pairBytes, Nat.add_assoc] using
    Nat.add_le_add_left (Nat.add_le_add_right hn (cleanupCost pair)) (prepareCost ctx pair)

def pairCount (ctx : Context) (pair : PlanPair) : ℕ :=
  PaddedCompletion.trueCount (pairStream ctx pair [])

def streamedPairs (ctx : Context) (pairs : List PlanPair) (stream : List Bool) : List Bool :=
  pairs.foldl (fun acc pair => pairStream ctx pair acc) stream

def score (ctx : Context) (pairs : List PlanPair) : ℕ :=
  PaddedCompletion.trueCount (streamedPairs ctx pairs [])

theorem pairStream_length (ctx : Context) (pair : PlanPair) (stream : List Bool) :
    (pairStream ctx pair stream).length =
      ctx.alphabet.length ^ ctx.depth.length + stream.length := by
  simp [pairStream, CollisionTupleProgram.streamed_length, TupleProgram.generated_count]

theorem pairStream_trueCount (ctx : Context) (pair : PlanPair) (stream : List Bool) :
    PaddedCompletion.trueCount (pairStream ctx pair stream) =
      pairCount ctx pair + PaddedCompletion.trueCount stream := by
  unfold pairCount pairStream
  rw [CollisionTupleProgram.streamed_trueCount, CollisionTupleProgram.streamed_trueCount]
  simp [PaddedCompletion.trueCount, PaddedCompletion.successful]

theorem streamedPairs_length (ctx : Context) (pairs : List PlanPair) (stream : List Bool) :
    (streamedPairs ctx pairs stream).length =
      pairs.length * ctx.alphabet.length ^ ctx.depth.length + stream.length := by
  induction pairs generalizing stream with
  | nil => simp [streamedPairs]
  | cons pair pairs ih =>
    change (streamedPairs ctx pairs (pairStream ctx pair stream)).length = _
    rw [ih, pairStream_length]
    simp only [List.length_cons]
    ring

theorem streamedPairs_trueCount (ctx : Context) (pairs : List PlanPair) (stream : List Bool) :
    PaddedCompletion.trueCount (streamedPairs ctx pairs stream) =
      (pairs.map (pairCount ctx)).sum + PaddedCompletion.trueCount stream := by
  induction pairs generalizing stream with
  | nil => simp [streamedPairs]
  | cons pair pairs ih =>
    change PaddedCompletion.trueCount (streamedPairs ctx pairs (pairStream ctx pair stream)) = _
    rw [ih, pairStream_trueCount]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem score_eq_sum (ctx : Context) (pairs : List PlanPair) :
    score ctx pairs = (pairs.map (pairCount ctx)).sum := by
  rw [score, streamedPairs_trueCount]
  simp [PaddedCompletion.trueCount, PaddedCompletion.successful]

theorem score_le_leafCount (ctx : Context) (pairs : List PlanPair) :
    score ctx pairs ≤ pairs.length * ctx.alphabet.length ^ ctx.depth.length := by
  have h := List.length_filter_le id (streamedPairs ctx pairs [])
  simpa [score, PaddedCompletion.trueCount, PaddedCompletion.successful,
    streamedPairs_length] using h

def validPayload (ctx : Context) (bits : List Bool) : Prop :=
  ∃ pair : PlanPair, bits = pairBytes pair ∧ ValidPair ctx pair

def invariant (ctx : Context) (d : Data) : Prop :=
  ∃ stream : List Bool, d = baseState ctx stream

def effect (ctx : Context) (bits : List Bool) (a b : Data) : Prop :=
  b.stacks 11 = pairStream ctx (readPair bits) (a.stacks 11)

theorem callback_contract (ctx : Context) (hc : ctx.Valid) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost ctx) (invariant ctx) (effect ctx) (validPayload ctx) := by
  rintro bits tail base ⟨pair, rfl, hp⟩ ⟨stream, rfl⟩
  obtain ⟨n, hn, he⟩ := callback_eval ctx hc pair hp tail stream
  refine ⟨n, baseState ctx (pairStream ctx pair stream), hn, ⟨_, rfl⟩, ?_, he⟩
  simp [effect, baseState]

private theorem unread_false (records : List (List Bool)) :
    RecordPrograms.unread (fun _ => false) records [] = [] := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa only [RecordPrograms.unread, Bool.false_eq_true, ite_false] using ih

private theorem any_false (records : List (List Bool)) :
    records.any (fun _ => false) = false := by
  induction records <;> simp_all

theorem records_fold (ctx : Context) (pairs : List PlanPair) (stream : List Bool) :
    (pairs.map pairBytes).foldl (fun acc bits => pairStream ctx (readPair bits) acc) stream =
      streamedPairs ctx pairs stream := by
  induction pairs generalizing stream with
  | nil => rfl
  | cons pair pairs ih =>
    simpa only [List.map_cons, List.foldl_cons, readPair_pairBytes, streamedPairs] using
      ih (pairStream ctx pair stream)

abbrev loop : Cmd 13 26 := RecordPrograms.iterate ports callback

def inputState (ctx : Context) (pairs : List PlanPair) : Data :=
  RecordPrograms.state ports (baseState ctx []) false false false (pairRecords pairs) []

theorem inputState_regs (ctx : Context) (pairs : List PlanPair) :
    (inputState ctx pairs).regs = fun _ => false := by
  funext j
  fin_cases j <;> simp [inputState, RecordPrograms.state, ports, baseState]

theorem inputState_stacks (ctx : Context) (pairs : List PlanPair) :
    (inputState ctx pairs).stacks = fun j =>
      if j = 3 then ctx.width else if j = 13 then ctx.current.flatten
      else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
      else if j = 23 then ctx.depth else if j = 20 then pairRecords pairs else [] := by
  funext j
  fin_cases j <;> simp [inputState, RecordPrograms.state, ports, baseState]

theorem loop_eval (ctx : Context) (hc : ctx.Valid) (pairs : List PlanPair)
    (hp : ∀ pair ∈ pairs, ValidPair ctx pair) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost ctx) (pairs.map pairBytes),
      Eval loop n (inputState ctx pairs) (baseState ctx (streamedPairs ctx pairs [])) := by
  have hv : ∀ bits ∈ pairs.map pairBytes, validPayload ctx bits := by
    intro bits hbits
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hbits
    exact ⟨pair, rfl, hp pair hpair⟩
  obtain ⟨n, next, hn, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost ctx) (invariant ctx) (effect ctx)
    (validPayload ctx) (callback_contract ctx hc) (pairs.map pairBytes) []
    (baseState ctx []) hv ⟨[], rfl⟩ false false false
  obtain ⟨stream, rfl⟩ := hnext
  have hout : stream = streamedPairs ctx pairs [] := by
    have h := history.fold_of_false (by simp) (fun d => d.stacks 11)
      (fun acc bits => pairStream ctx (readPair bits) acc) (fun _ _ _ h => h)
    simpa only [baseState, Fin.reduceEq, ite_false, ite_true, records_fold] using h
  subst stream
  have hf : RecordPrograms.state ports (baseState ctx (streamedPairs ctx pairs []))
      false true false [] [] = baseState ctx (streamedPairs ctx pairs []) := by
    apply RecordPrograms.state_eq_self <;> simp [ports, baseState]
  refine ⟨n, hn, ?_⟩
  simpa only [any_false, unread_false, hf, ProgramEncoding.encodeRecords,
    inputState, pairRecords, List.append_nil, loop] using he

def tallyRegs : Fin 2 → Fin 13 := Fin.castAdd 11
def tallyPorts : Fin 2 → Fin 26 := fun i => if i = 0 then 11 else 18

theorem tallyRegs_injective : Function.Injective tallyRegs := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 13 => k.val) h)

theorem tallyPorts_injective : Function.Injective tallyPorts := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [tallyPorts]

abbrev tally : Cmd 13 26 :=
  .call (ProgramLinking.liftProgram UnaryTally.program tallyRegs tallyPorts)

def afterTally (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 11 []) 18
      (List.replicate (PaddedCompletion.trueCount (d.stacks 11)) false ++ d.stacks 18)⟩

theorem tally_eval (d : Data) :
    Eval tally (UnaryTally.steps (d.stacks 11)) d (afterTally d) := by
  let a : StructuredProgram.State 2 2 :=
    ⟨d.regs ∘ tallyRegs, UnaryTally.pairStacks (d.stacks 11) (d.stacks 18)⟩
  let b : StructuredProgram.State 2 2 :=
    ⟨fun _ => false, UnaryTally.pairStacks []
      (List.replicate (PaddedCompletion.trueCount (d.stacks 11)) false ++ d.stacks 18)⟩
  have ha : embedState tallyRegs tallyPorts d a = d := by
    apply embedState_eq _ _ tallyRegs_injective tallyPorts_injective
    · intro i; rfl
    · intro i; fin_cases i <;> simp [a, tallyPorts, UnaryTally.pairStacks]
    · intros; rfl
    · intros; rfl
  have hb : embedState tallyRegs tallyPorts d b = afterTally d := by
    apply embedState_eq _ _ tallyRegs_injective tallyPorts_injective
    · intro i; fin_cases i <;> simp [b, afterTally, tallyRegs, readRegs]
    · intro i; fin_cases i <;> simp [b, afterTally, tallyPorts, UnaryTally.pairStacks]
    · intro j hj
      have h0 : j ≠ 0 := fun h => hj ⟨0, by simpa [tallyRegs] using h.symm⟩
      have h1 : j ≠ 1 := fun h => hj ⟨1, by simpa [tallyRegs] using h.symm⟩
      simp [afterTally, readRegs, h0, h1]
    · intro j hj
      have h11 : j ≠ 11 := fun h => hj ⟨0, by simpa [tallyPorts] using h.symm⟩
      have h18 : j ≠ 18 := fun h => hj ⟨1, by simpa [tallyPorts] using h.symm⟩
      simp [afterTally, h11, h18]
  have ht := UnaryTally.tally_trace (d.regs ∘ tallyRegs) (d.stacks 11) (d.stacks 18)
  have he := eval_call_lifted UnaryTally.program tallyRegs tallyPorts d
    tallyRegs_injective tallyPorts_injective (a := a) (b := b) ht
  simpa only [ha, hb, tally] using he

abbrev command : Cmd 13 26 := .seq loop tally

abbrev program : Program 13 26 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 20 18

def outputState (ctx : Context) (pairs : List PlanPair) : Data :=
  afterTally (baseState ctx (streamedPairs ctx pairs []))

@[simp] theorem outputState_output (ctx : Context) (pairs : List PlanPair) :
    (outputState ctx pairs).stacks 18 = UnaryCompare.encode (score ctx pairs) := by
  simp [outputState, afterTally, baseState, score, UnaryCompare.encode]

theorem outputState_stacks (ctx : Context) (pairs : List PlanPair) :
    (outputState ctx pairs).stacks = fun j =>
      if j = 3 then ctx.width else if j = 13 then ctx.current.flatten
      else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
      else if j = 23 then ctx.depth else if j = 18 then UnaryCompare.encode (score ctx pairs)
      else [] := by
  funext j
  fin_cases j <;> simp [outputState, afterTally, baseState, score, UnaryCompare.encode]

theorem outputState_regs (ctx : Context) (pairs : List PlanPair) :
    (outputState ctx pairs).regs = fun j => decide (j = 11) := by
  funext j
  fin_cases j <;> simp [outputState, afterTally, baseState, readRegs]

def sourceBudget (ctx : Context) (pairs : List PlanPair) : ℕ :=
  RecordPrograms.budget (callbackCost ctx) (pairs.map pairBytes) +
    5 * (pairs.length * ctx.alphabet.length ^ ctx.depth.length) + 7

/-- One fixed record iterator executes every pair's real generator/collision
program, then tallies its complete concatenated stream. -/
theorem program_run (ctx : Context) (pairs : List PlanPair) (hc : ctx.Valid)
    (hp : ∀ pair ∈ pairs, ValidPair ctx pair) :
    RunsIn program (sourceBudget ctx pairs)
      ((inputState ctx pairs).withPC (some program.entry))
      ((outputState ctx pairs).withPC none) := by
  obtain ⟨n, hn, he⟩ := loop_eval ctx hc pairs hp
  let d := baseState ctx (streamedPairs ctx pairs [])
  have ht := tally_eval d
  have hlen : (d.stacks 11).length = pairs.length * ctx.alphabet.length ^ ctx.depth.length := by
    simp [d, baseState, streamedPairs_length]
  have hcost := UnaryTally.steps_le (d.stacks 11)
  rw [hlen] at hcost
  refine ⟨n + UnaryTally.steps (d.stacks 11) + 1, ?_, ?_⟩
  · dsimp [sourceBudget]
    omega
  · exact compiled_halt_trace (he.seq ht) 20 18

theorem primitive_run (ctx : Context) (pairs : List PlanPair) (hc : ctx.Valid)
    (hp : ∀ pair ∈ pairs, ValidPair ctx pair) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceBudget ctx pairs)
      (primitiveCfg program ((inputState ctx pairs).withPC (some program.entry)))
      (primitiveCfg program ((outputState ctx pairs).withPC none)) :=
  BitProgram.primitive_execution program (program_run ctx pairs hc hp)

/-- Any runtime mapping of the full ordered vertex-pair list has D squared
records, including maps whose selected plans depend on both vertices. -/
def allPairPlans {A : Type*} (vertices : List A) (plans : A × A → PlanPair) : List PlanPair :=
  (vertices ×ˢ vertices).map plans

@[simp] theorem allPairPlans_length {A : Type*} (vertices : List A)
    (plans : A × A → PlanPair) :
    (allPairPlans vertices plans).length = vertices.length ^ 2 := by
  simpa only [allPairPlans, List.length_map, pow_two] using
    List.length_product vertices vertices

/-- The exact D squared times N squared leaf count is derived from the actual
pair list and generated tuple depth. -/
theorem streamedPairs_length_allPairs {A : Type*} (ctx : Context) (vertices : List A)
    (plans : A × A → PlanPair) (Δ : ℕ) (hdepth : ctx.depth.length = 2 * (Δ + 1))
    (stream : List Bool) :
    (streamedPairs ctx (allPairPlans vertices plans) stream).length =
      vertices.length ^ 2 * (ctx.alphabet.length ^ (Δ + 1)) ^ 2 + stream.length := by
  rw [streamedPairs_length, allPairPlans_length, hdepth, Nat.mul_comm 2 (Δ + 1), pow_mul]

theorem sourceBudget_allPairs {A : Type*} (ctx : Context) (vertices : List A)
    (plans : A × A → PlanPair) (Δ : ℕ) (hdepth : ctx.depth.length = 2 * (Δ + 1)) :
    sourceBudget ctx (allPairPlans vertices plans) =
      RecordPrograms.budget (callbackCost ctx)
        ((allPairPlans vertices plans).map pairBytes) +
        5 * (vertices.length ^ 2 * (ctx.alphabet.length ^ (Δ + 1)) ^ 2) + 7 := by
  rw [sourceBudget, allPairPlans_length, hdepth, Nat.mul_comm 2 (Δ + 1), pow_mul]

theorem sourceBudget_eq (ctx : Context) (pairs : List PlanPair) :
    sourceBudget ctx pairs =
      6 * (pairs.map (fun pair => (pairBytes pair).length)).sum +
      (pairs.map (fun pair => callbackCost ctx (pairBytes pair))).sum +
      7 * pairs.length + 5 * (pairs.length * ctx.alphabet.length ^ ctx.depth.length) + 7 := by
  simp only [sourceBudget, RecordPrograms.budget_eq, List.map_map, List.length_map,
    Function.comp_def]

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
