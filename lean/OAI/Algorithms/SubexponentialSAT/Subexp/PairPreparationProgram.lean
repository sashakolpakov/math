import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ActivePlanProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectionTableProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.SelectorPairProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PairPlanPreparation
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms

namespace OAI.Algorithms

/-!
# Preparing all selected pair plans once per assignment step

The fixed program preserves the full seed-index records, original pair
records, seed count, and processed counter. It computes the next cutoff,
builds each pair's actual selection table, and emits selected pair records.
The candidate value is not an input to this preparation phase.
-/

namespace SubexponentialSAT.Subexp.PairPreparationProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 16 34
abbrev PlanPair := PairScoreProgram.PlanPair

def ports : RecordPrograms.Ports 16 34 where
  tag := 13
  present := 14
  found := 15
  source := 20
  payload := 21
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def activeRegs : Fin 10 → Fin 16 := Fin.castAdd 6
def activeStacks : Fin 12 → Fin 34 := Fin.castAdd 22
def tableRegs : Fin 3 → Fin 16 := Fin.castAdd 13
def tableStacks : Fin 6 → Fin 34 := Fin.castAdd 28
def selectorRegs : Fin 8 → Fin 16 := Fin.castAdd 8

/-- Stack 7 holds the cutoff throughout the pair loop and is excluded. -/
def selectorStacks : Fin 12 → Fin 34 := ![0, 1, 2, 4, 5, 11, 6, 3, 8, 9, 10, 29]

def reverseStacks : Fin 4 → Fin 34 := ![29, 1, 28, 4]

theorem activeRegs_injective : Function.Injective activeRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem activeStacks_injective : Function.Injective activeStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 34 => x.val) h)

theorem tableRegs_injective : Function.Injective tableRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem tableStacks_injective : Function.Injective tableStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 34 => x.val) h)

theorem selectorRegs_injective : Function.Injective selectorRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

theorem selectorStacks_injective : Function.Injective selectorStacks := by decide
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev activeCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram ActivePlanProgram.program activeRegs activeStacks)

abbrev tableCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SelectionTableProgram.program tableRegs tableStacks)

abbrev selectorCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SelectorPairProgram.program selectorRegs selectorStacks)

abbrev reverseCall : Cmd 16 34 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram
    tableRegs reverseStacks)

abbrev copy (src dst : Fin 34) : Cmd 16 34 := .call (copyProgram src dst 4 (0 : Fin 16) 1)
abbrev clear (src : Fin 34) : Cmd 16 34 := .call (clearProgram src (0 : Fin 16) 1)
abbrev move (src dst : Fin 34) : Cmd 16 34 := .seq (copy src dst) (clear src)

def copied (a : Data) (src dst : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

def cleared (a : Data) (src : Fin 34) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks src a.stacks⟩

def moved (a : Data) (src dst : Fin 34) : Data := cleared (copied a src dst) src

theorem copy_eval (a : Data) (src dst : Fin 34) (hsd : src ≠ dst)
    (hs4 : src ≠ 4) (h4d : (4 : Fin 34) ≠ dst) (h4 : a.stacks 4 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied a src dst) :=
  TupleProgram.copy_eval src dst 4 (0 : Fin 16) 1 hsd hs4 h4d (by decide) a h4

theorem clear_eval (a : Data) (src : Fin 34) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  TupleProgram.clear_eval src (0 : Fin 16) 1 a

theorem move_eval (a : Data) (src dst : Fin 34) (hsd : src ≠ dst)
    (hs4 : src ≠ 4) (h4d : (4 : Fin 34) ≠ dst) (h4 : a.stacks 4 = []) :
    Eval (move src dst) (9 * (a.stacks src).length + 8) a (moved a src dst) := by
  have h := (copy_eval a src dst hsd hs4 h4d h4).seq (clear_eval (copied a src dst) src)
  convert h using 1 <;> simp [moved, copied, copyStacks, hsd]
  omega

abbrev resetList : List (Fin 16) → StructuredProgram.Cmd 16 34
  | [] => .skip
  | i :: rest => .seq (.atom (.set i false)) (resetList rest)

abbrev resetInner : Cmd 16 34 := .base (resetList [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
abbrev resetTable : Cmd 16 34 := .base (resetList [0, 1, 2])
abbrev resetAll : Cmd 16 34 := .base (resetList (List.finRange 16))

def resetValues (indices : List (Fin 16)) (regs : Fin 16 → Bool) : Fin 16 → Bool :=
  indices.foldl (fun rs i => Function.update rs i false) regs

theorem resetList_eval (indices : List (Fin 16)) (a : Data) :
    StructuredProgram.Eval (resetList indices) indices.length a
      ⟨resetValues indices a.regs, a.stacks⟩ := by
  induction indices generalizing a with
  | nil => exact .skip a
  | cons i rest ih =>
    have h := (StructuredProgram.Eval.atom (.set i false) a).seq
      (ih ((StructuredProgram.Atom.set i false).eval a))
    simpa [resetList, resetValues, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      StructuredProgram.State.withPC, execInstr, Nat.add_comm] using h

def innerReset (a : Data) : Data :=
  ⟨fun j => if j.val < 13 then false else a.regs j, a.stacks⟩

theorem resetInner_eval (a : Data) : Eval resetInner 13 a (innerReset a) := by
  have h := resetList_eval [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] a
  have hr : resetValues [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] a.regs =
      fun j => if j.val < 13 then false else a.regs j := by
    funext j
    fin_cases j <;> simp [resetValues]
  rw [hr] at h
  exact Eval.base h

def tableReset (a : Data) : Data :=
  ⟨fun j => if j.val < 3 then false else a.regs j, a.stacks⟩

theorem resetTable_eval (a : Data) : Eval resetTable 3 a (tableReset a) := by
  have h := resetList_eval [0, 1, 2] a
  have hr : resetValues [0, 1, 2] a.regs =
      fun j => if j.val < 3 then false else a.regs j := by
    funext j
    fin_cases j <;> simp [resetValues]
  rw [hr] at h
  exact Eval.base h

theorem resetAll_eval (a : Data) : Eval resetAll 16 a ⟨fun _ => false, a.stacks⟩ := by
  have h := resetList_eval (List.finRange 16) a
  have hr : resetValues (List.finRange 16) a.regs = fun _ => false := by
    funext j
    fin_cases j <;> rfl
  rw [hr] at h
  exact Eval.base h

def sequence : List (Cmd 16 34) → Cmd 16 34
  | [] => .base .skip
  | c :: cs => .seq c (sequence cs)

/-- Each operation below is a fixed instruction table or a fixed finite
composition. In particular, the selection table is actually generated. -/
def callback : Cmd 16 34 := sequence [
  PairPlanPreparation.parsePair,
  PairPlanPreparation.buildUnion,
  copy 30 5,
  activeCall,
  clear 6,
  move 11 0,
  copy 32 2,
  resetTable,
  tableCall,
  clear 2,
  PairPlanPreparation.reverseQueries,
  selectorCall,
  clear 3,
  resetInner]

/-- Inputs: 30 seed-index records, 31 raw pair records, 32 unary seed count,
33 unary processed count. Output: 29 selected pair records in input order.
Every source is copied before it is scanned or changed. -/
abbrev command : Cmd 16 34 := sequence [
  copy 31 20,
  copy 33 7,
  TupleProgram.pushConst 7 0 true,
  TupleProgram.pushConst 29 0 false,
  resetAll,
  RecordPrograms.iterate ports callback,
  clear 7,
  TupleProgram.pushConst 28 0 false,
  reverseCall,
  move 28 29,
  resetAll]

abbrev program : Program 16 34 (size command + 1) := compiled command 31 29

def remaining (M processed : ℕ) (pair : PlanPair) : List ℕ :=
  ActivePlanProgram.active (List.range M) (pair.1.reverse ++ pair.2) (processed + 1)

def selectedPair (M processed : ℕ) (pair : PlanPair) : PlanPair :=
  (pair.1.map (ReadPlan.selectPosition M (remaining M processed pair)),
   pair.2.map (ReadPlan.selectPosition M (remaining M processed pair)))

def selectedPairs (M processed : ℕ) (pairs : List PlanPair) : List PlanPair :=
  pairs.map (selectedPair M processed)

structure Context where
  seedCount : ℕ
  processedBits : List Bool
  pairs : List PlanPair

private theorem activeUnary_eq : ActivePlanProgram.unary = SelectionTableProgram.unary := rfl

def seedBytes (M : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords ((List.range M).map SelectionTableProgram.unary)

/-- Only the four immutable inputs are populated initially. In particular,
processed bits are arbitrary; their length is the logical processed count. -/
def inputState (ctx : Context) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun j =>
    if j = 30 then seedBytes ctx.seedCount
    else if j = 31 then PairScoreProgram.pairRecords ctx.pairs
    else if j = 32 then SelectionTableProgram.unary ctx.seedCount
    else if j = 33 then ctx.processedBits else []⟩

def baseState (ctx : Context) (acc : List Bool) : Data :=
  ⟨fun _ => false, fun j =>
    if j = 7 then true :: ctx.processedBits
    else if j = 29 then acc else (inputState ctx (fun _ => false)).stacks j⟩

def outputState (ctx : Context) : Data :=
  ⟨fun _ => false, Function.update (inputState ctx (fun _ => false)).stacks 29
    (PairScoreProgram.pairRecords (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs))⟩

def callbackCost (ctx : Context) (pair : PlanPair) : ℕ :=
  let l := pair.1.map SelectionTableProgram.unary
  let r := pair.2.map SelectionTableProgram.unary
  let rem := remaining ctx.seedCount ctx.processedBits.length pair
  let unionBytes := ProgramEncoding.encodeRecords (l.reverse ++ r)
  let remBytes := ProgramEncoding.encodeRecords (rem.map SelectionTableProgram.unary)
  let table := SelectorProgram.selectionEntries ctx.seedCount rem
  [PairPlanPreparation.parseCost l r,
   17 * (ProgramEncoding.encodeRecords l).length +
     7 * (ProgramEncoding.encodeRecords r).length + 10,
   7 * (seedBytes ctx.seedCount).length + 5,
   ActivePlanProgram.traceBoundThreshold (List.range ctx.seedCount)
     (pair.1.reverse ++ pair.2) (true :: ctx.processedBits),
   2 * unionBytes.length + 3,
   9 * remBytes.length + 8,
   7 * ctx.seedCount + 5,
   3,
   SelectionTableProgram.traceCost ctx.seedCount rem,
   2 * (ctx.seedCount + rem.length) + 3,
   10 * (ProgramEncoding.encodeRecords l).length +
     10 * (ProgramEncoding.encodeRecords r).length + 9,
   SelectorPairProgram.cost table (l.reverse) (r.reverse),
   2 * (SelectionTableProgram.tableBytes ctx.seedCount rem).length + 3,
   13].sum

def loopCost (ctx : Context) : List PlanPair → ℕ
  | [] => 1
  | pair :: rest => 6 * (PairScoreProgram.pairBytes pair).length +
      callbackCost ctx pair + 7 + loopCost ctx rest

/-- This bound sums the costs of the actual called instruction tables and
record scans. It is not an assumed bound on an abstract preparation function. -/
def traceBound (ctx : Context) : ℕ :=
  let selected := selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs
  7 * (PairScoreProgram.pairRecords ctx.pairs).length + 5 +
  (7 * ctx.processedBits.length + 5) + 2 + 2 + 16 +
  (2 + loopCost ctx ctx.pairs) + (2 * (ctx.processedBits.length + 1) + 3) + 2 +
  10 * (PairScoreProgram.pairRecords selected.reverse).length +
  (9 * (PairScoreProgram.pairRecords selected).length + 8) + 16 + 1

def prefixRegs {n : ℕ} (small : Fin n → Bool) (old : Fin 16 → Bool) : Fin 16 → Bool :=
  fun j => if hj : j.val < n then small ⟨j.val, hj⟩ else old j

def activeAfter (a : Data) (rf : Fin 10 → Bool) (seeds plan : List ℕ)
    (threshold : List Bool) : Data :=
  ⟨prefixRegs rf a.regs,
    Function.update (Function.update a.stacks 5 []) 11
      (ProgramEncoding.encodeRecords
        (ActivePlanProgram.indexRecords (ActivePlanProgram.active seeds plan threshold.length)))⟩

theorem activeCall_eval (a : Data) (seeds plan : List ℕ) (threshold : List Bool)
    (hs : ∀ i, a.stacks (activeStacks i) =
      (ActivePlanProgram.inputStateThreshold (fun j => a.regs (activeRegs j))
        seeds plan threshold).stacks i) :
    ∃ n ≤ ActivePlanProgram.traceBoundThreshold seeds plan threshold, ∃ rf,
      Eval activeCall n a (activeAfter a rf seeds plan threshold) := by
  obtain ⟨rf, n, hn, ht⟩ := ActivePlanProgram.program_runsIn_threshold
    (fun j => a.regs (activeRegs j)) seeds plan threshold
  have hin : embedState activeRegs activeStacks a
      (ActivePlanProgram.inputStateThreshold (fun j => a.regs (activeRegs j))
        seeds plan threshold) = a := by
    apply SelectorMapProgram.embed_eq _ _ activeRegs_injective activeStacks_injective
    · intro i; rfl
    · exact hs
    · intro j hj; rfl
    · intro j hj; rfl
  have hout : embedState activeRegs activeStacks a
      (ActivePlanProgram.outputStateThreshold rf seeds plan threshold) =
      activeAfter a rf seeds plan threshold := by
    apply SelectorMapProgram.embed_eq _ _ activeRegs_injective activeStacks_injective
    · intro i
      simp [activeAfter, prefixRegs, activeRegs
        ]
    · intro i
      have hi := hs i
      fin_cases i <;>
        simp_all [activeAfter, activeStacks, ActivePlanProgram.inputStateThreshold,
          ActivePlanProgram.outputStateThreshold, ActivePlanProgram.state]
    · intro j hj
      have hge : 10 ≤ j.val := by
        by_contra h
        have hlt : j.val < 10 := by omega
        exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
      simp [activeAfter, prefixRegs, Nat.not_lt.mpr hge]
    · intro j hj
      have h5 : j ≠ 5 := by
        intro h; subst j; exact hj ⟨5, rfl⟩
      have h11 : j ≠ 11 := by
        intro h; subst j; exact hj ⟨11, rfl⟩
      simp [activeAfter, h5, h11]
  refine ⟨n, hn, rf, ?_⟩
  have he := eval_call_lifted ActivePlanProgram.program activeRegs activeStacks a
    activeRegs_injective activeStacks_injective ht
  simpa only [activeCall, hin, hout] using he

def tableAfter (a : Data) (M : ℕ) (remaining : List ℕ) : Data :=
  ⟨prefixRegs (fun _ : Fin 3 => false) a.regs,
    Function.update (Function.update (Function.update a.stacks 0 []) 2
      (SelectionTableProgram.unary (M + remaining.length))) 3
      (SelectionTableProgram.tableBytes M remaining)⟩

theorem tableCall_eval (a : Data) (M : ℕ) (remaining : List ℕ)
    (hr : ∀ i, a.regs (tableRegs i) = false)
    (hs : ∀ i, a.stacks (tableStacks i) = (SelectionTableProgram.inputState M remaining).stacks i) :
    Eval tableCall (SelectionTableProgram.traceCost M remaining) a (tableAfter a M remaining) := by
  have hin : embedState tableRegs tableStacks a (SelectionTableProgram.inputState M remaining) = a := by
    apply SelectorMapProgram.embed_eq _ _ tableRegs_injective tableStacks_injective
    · intro i
      have hi := hr i
      fin_cases i <;> simpa [SelectionTableProgram.inputState, SelectionTableProgram.baseState,
        SelectionTableProgram.ports, SelectionTableProgram.state, RecordPrograms.state] using hi
    · exact hs
    · intro j hj; rfl
    · intro j hj; rfl
  have hout : embedState tableRegs tableStacks a (SelectionTableProgram.outputState M remaining) =
      tableAfter a M remaining := by
    apply SelectorMapProgram.embed_eq _ _ tableRegs_injective tableStacks_injective
    · intro i
      fin_cases i <;> simp [tableAfter, prefixRegs, tableRegs, SelectionTableProgram.outputState,
        SelectionTableProgram.state]
    · intro i
      have hi := hs i
      fin_cases i <;>
        simp_all [tableAfter, tableStacks, SelectionTableProgram.inputState,
          SelectionTableProgram.outputState, SelectionTableProgram.baseState,
          SelectionTableProgram.state, SelectionTableProgram.ports, RecordPrograms.state]
    · intro j hj
      have hge : 3 ≤ j.val := by
        by_contra h
        have hlt : j.val < 3 := by omega
        exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
      simp [tableAfter, prefixRegs, Nat.not_lt.mpr hge]
    · intro j hj
      have h0 : j ≠ 0 := by intro h; subst j; exact hj ⟨0, rfl⟩
      have h2 : j ≠ 2 := by intro h; subst j; exact hj ⟨2, rfl⟩
      have h3 : j ≠ 3 := by intro h; subst j; exact hj ⟨3, rfl⟩
      simp [tableAfter, h0, h2, h3]
  have he := eval_call_lifted SelectionTableProgram.program tableRegs tableStacks a
    tableRegs_injective tableStacks_injective (SelectionTableProgram.program_trace M remaining)
  simpa only [tableCall, hin, hout] using he

def selectorAfter (a : Data) (rf : Fin 8 → Bool)
    (records : List (List Bool × List Bool)) (left right : List (List Bool)) : Data :=
  ⟨prefixRegs rf a.regs,
    Function.update (Function.update (Function.update a.stacks 6 []) 9 []) 29
      (TupleProgram.prependRecord
        (SelectorPairProgram.payload (SelectorPairProgram.planBytes records left)
          (SelectorPairProgram.planBytes records right)) (a.stacks 29))⟩

theorem selectorCall_eval (a : Data) (records : List (List Bool × List Bool))
    (left right : List (List Bool))
    (hs : ∀ i, a.stacks (selectorStacks i) =
      (SelectorPairProgram.state (fun j => a.regs (selectorRegs j))
        (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
        [] (ProgramEncoding.encodeRecords right) [] (a.stacks 29)).stacks i) :
    ∃ n ≤ SelectorPairProgram.cost records left right, ∃ rf,
      Eval selectorCall n a (selectorAfter a rf records left right) := by
  obtain ⟨n, hn, rf, ht⟩ := SelectorPairProgram.program_trace records left right
    (fun j => a.regs (selectorRegs j)) (a.stacks 29)
  have hin : embedState selectorRegs selectorStacks a
      (SelectorPairProgram.state (fun j => a.regs (selectorRegs j))
        (ProgramEncoding.encodeRecords left) (SelectorProgram.rawRecords records)
        [] (ProgramEncoding.encodeRecords right) [] (a.stacks 29)) = a := by
    apply SelectorMapProgram.embed_eq _ _ selectorRegs_injective selectorStacks_injective
    · intro i; rfl
    · exact hs
    · intro j hj; rfl
    · intro j hj; rfl
  have hout : embedState selectorRegs selectorStacks a
      (SelectorPairProgram.state rf [] (SelectorProgram.rawRecords records) [] [] []
        (TupleProgram.prependRecord
          (SelectorPairProgram.payload (SelectorPairProgram.planBytes records left)
            (SelectorPairProgram.planBytes records right)) (a.stacks 29))) =
      selectorAfter a rf records left right := by
    apply SelectorMapProgram.embed_eq _ _ selectorRegs_injective selectorStacks_injective
    · intro i
      simp [selectorAfter, prefixRegs, selectorRegs, SelectorPairProgram.state]
    · intro i
      have hi := hs i
      fin_cases i <;> simp_all [selectorAfter, selectorStacks, SelectorPairProgram.state]
    · intro j hj
      have hge : 8 ≤ j.val := by
        by_contra h
        have hlt : j.val < 8 := by omega
        exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
      simp [selectorAfter, prefixRegs, Nat.not_lt.mpr hge]
    · intro j hj
      have h6 : j ≠ 6 := by intro h; subst j; exact hj ⟨6, rfl⟩
      have h9 : j ≠ 9 := by intro h; subst j; exact hj ⟨9, rfl⟩
      have h29 : j ≠ 29 := by intro h; subst j; exact hj ⟨11, rfl⟩
      simp [selectorAfter, h6, h9, h29]
  refine ⟨n, hn, rf, ?_⟩
  have he := eval_call_lifted SelectorPairProgram.program selectorRegs selectorStacks a
    selectorRegs_injective selectorStacks_injective ht
  simpa only [selectorCall, hin, hout] using he

theorem selectedPayload_eq (M processed : ℕ) (pair : PlanPair) :
    SelectorPairProgram.payload
      (SelectorPairProgram.planBytes (SelectorProgram.selectionEntries M (remaining M processed pair))
        (pair.1.reverse.map SelectorProgram.unaryIndex))
      (SelectorPairProgram.planBytes (SelectorProgram.selectionEntries M (remaining M processed pair))
        (pair.2.reverse.map SelectorProgram.unaryIndex)) =
    PairScoreProgram.pairBytes (selectedPair M processed pair) := by
  rw [SelectorPairProgram.planBytes_selection, SelectorPairProgram.planBytes_selection]
  simp [SelectorPairProgram.payload, PairScoreProgram.pairBytes, selectedPair,
    CollisionStreamProgram.planBytes, GatherProgram.indexRecords, List.map_map,
    SelectorProgram.unaryIndex, Function.comp_def]

def callbackFinal (ctx : Context) (pair : PlanPair) (acc : List PlanPair)
    (tail : List Bool) (rf3 : Fin 10 → Bool) (rf11 : Fin 8 → Bool) : Data :=
  let l := pair.1.map SelectionTableProgram.unary
  let r := pair.2.map SelectionTableProgram.unary
  let rem := remaining ctx.seedCount ctx.processedBits.length pair
  let table := SelectorProgram.selectionEntries ctx.seedCount rem
  let a0 := RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
    false true false tail (PairScoreProgram.pairBytes pair).reverse
  let a1 := PairPlanPreparation.parsed a0 l r
  let a2 := PairPlanPreparation.unionPrepared a1 l r
  let a3 := copied a2 30 5
  let a4 := activeAfter a3 rf3 (List.range ctx.seedCount)
    (pair.1.reverse ++ pair.2) (true :: ctx.processedBits)
  let a5 := cleared a4 6
  let a6 := moved a5 11 0
  let a7 := copied a6 32 2
  let a8 := tableReset a7
  let a9 := tableAfter a8 ctx.seedCount rem
  let a10 := cleared a9 2
  let a11 := PairPlanPreparation.queriesPrepared a10 l r
  let a12 := selectorAfter a11 rf11 table l.reverse r.reverse
  let a13 := cleared a12 3
  innerReset a13

private theorem callbackFinal_eq (ctx : Context) (pair : PlanPair) (acc : List PlanPair)
    (tail : List Bool) (rf3 : Fin 10 → Bool) (rf11 : Fin 8 → Bool) :
    callbackFinal ctx pair acc tail rf3 rf11 = RecordPrograms.state ports
      (baseState ctx (PairScoreProgram.pairRecords
        (selectedPair ctx.seedCount ctx.processedBits.length pair :: acc)))
      false true false tail [] := by
  have hpay := selectedPayload_eq ctx.seedCount ctx.processedBits.length pair
  have hpay' : SelectorPairProgram.payload
      (SelectorPairProgram.planBytes
        (SelectorProgram.selectionEntries ctx.seedCount
          (remaining ctx.seedCount ctx.processedBits.length pair))
        (pair.1.map SelectionTableProgram.unary).reverse)
      (SelectorPairProgram.planBytes
        (SelectorProgram.selectionEntries ctx.seedCount
          (remaining ctx.seedCount ctx.processedBits.length pair))
        (pair.2.map SelectionTableProgram.unary).reverse) =
      PairScoreProgram.pairBytes (selectedPair ctx.seedCount ctx.processedBits.length pair) := by
    rw [show pair.1.map SelectionTableProgram.unary =
      pair.1.map SelectorProgram.unaryIndex by rfl]
    rw [show pair.2.map SelectionTableProgram.unary =
      pair.2.map SelectorProgram.unaryIndex by rfl]
    simpa only [List.map_reverse] using hpay
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    fin_cases j <;>
      simp [cleared, selectorAfter, PairPlanPreparation.queriesPrepared,
        tableAfter, tableReset, moved, copied, activeAfter, prefixRegs,
        PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
        RecordPrograms.state, ports, baseState, inputState, readRegs]
  · funext j
    fin_cases j <;>
      simp [cleared, clearStacks, selectorAfter,
        PairPlanPreparation.queriesPrepared, tableAfter, tableReset, moved, copied,
        copyStacks, activeAfter, PairPlanPreparation.unionPrepared,
        PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState,
        hpay', PairScoreProgram.pairRecords, ProgramEncoding.encodeRecords,
        TupleProgram.prependRecord, Encoding.encodeList]

/-- One actual pair-preparation call. Its effect is one framed selected pair
prepended to the existing output list, with the loop and source state framed. -/
theorem callback_eval (ctx : Context) (pair : PlanPair) (acc : List PlanPair)
    (tail : List Bool) :
    ∃ n ≤ callbackCost ctx pair,
      Eval callback n
        (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
          false true false tail (PairScoreProgram.pairBytes pair).reverse)
        (RecordPrograms.state ports
          (baseState ctx (PairScoreProgram.pairRecords
            (selectedPair ctx.seedCount ctx.processedBits.length pair :: acc)))
          false true false tail []) := by
  let l := pair.1.map SelectionTableProgram.unary
  let r := pair.2.map SelectionTableProgram.unary
  let rem := remaining ctx.seedCount ctx.processedBits.length pair
  let table := SelectorProgram.selectionEntries ctx.seedCount rem
  let a0 := RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
    false true false tail (PairScoreProgram.pairBytes pair).reverse
  let a1 := PairPlanPreparation.parsed a0 l r
  let a2 := PairPlanPreparation.unionPrepared a1 l r
  let a3 := copied a2 30 5
  have h0 : Eval PairPlanPreparation.parsePair (PairPlanPreparation.parseCost l r) a0 a1 := by
    apply PairPlanPreparation.parsePair_eval
    · simp only [a0, RecordPrograms.state, ports, Function.update_self]
      rfl
    all_goals simp [a0, RecordPrograms.state, ports, baseState, inputState]
  obtain ⟨n1, hn1, h1⟩ := PairPlanPreparation.buildUnion_eval a1 l r
    (by simp [a1, PairPlanPreparation.parsed])
    (by simp [a1, PairPlanPreparation.parsed])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
    (by simp [a1, a0, PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState])
  have h2 := copy_eval a2 30 5 (by decide) (by decide) (by decide)
    (by simp [a2, a1, a0, PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  obtain ⟨n3, hn3, rf3, h3⟩ := activeCall_eval a3 (List.range ctx.seedCount)
    (pair.1.reverse ++ pair.2) (true :: ctx.processedBits) (by
      intro i
      fin_cases i <;>
        simp [a3, a2, a1, a0, copied, copyStacks, PairPlanPreparation.unionPrepared,
          PairPlanPreparation.parsed, RecordPrograms.state, ports, baseState, inputState,
          activeStacks,
          ActivePlanProgram.indexRecords, seedBytes, l, r,
          SelectionTableProgram.unary, List.map_append, List.map_reverse, activeUnary_eq])
  let a4 := activeAfter a3 rf3 (List.range ctx.seedCount)
    (pair.1.reverse ++ pair.2) (true :: ctx.processedBits)
  let a5 := cleared a4 6
  let a6 := moved a5 11 0
  let a7 := copied a6 32 2
  let a8 := tableReset a7
  have h4 := clear_eval a4 6
  have h5 := move_eval a5 11 0 (by decide) (by decide) (by decide) (by
    simp [a5, a4, a3, a2, a1, a0, cleared, clearStacks, activeAfter, copied, copyStacks,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  have h6 := copy_eval a6 32 2 (by decide) (by decide) (by decide) (by
    simp [a6, a5, a4, a3, a2, a1, a0, moved, cleared, clearStacks, activeAfter,
      copied, copyStacks, PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  have h7 := resetTable_eval a7
  have h8 := tableCall_eval a8 ctx.seedCount rem
    (by intro i; simp [a8, tableReset, tableRegs])
    (by
      intro i
      fin_cases i <;>
        simp [a8, a7, a6, a5, a4, a3, a2, a1, a0, tableReset, moved,
          copied, copyStacks, cleared, clearStacks, activeAfter,
          PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
          RecordPrograms.state, ports, baseState, inputState, tableStacks,
          SelectionTableProgram.inputState, SelectionTableProgram.baseState,
          SelectionTableProgram.state, SelectionTableProgram.ports,
          SelectionTableProgram.indexRecords, SelectionTableProgram.unary,
          ActivePlanProgram.indexRecords, rem, remaining, activeUnary_eq])
  let a9 := tableAfter a8 ctx.seedCount rem
  let a10 := cleared a9 2
  have h9 := clear_eval a9 2
  obtain ⟨n10, hn10, h10⟩ := PairPlanPreparation.reverseQueries_eval a10 l r
    (by simp [a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, cleared, clearStacks,
      tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed])
    (by simp [a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, cleared, clearStacks,
      tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed])
    (by simp [a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0, cleared, clearStacks,
      tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
      PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
      RecordPrograms.state, ports, baseState, inputState])
  let a11 := PairPlanPreparation.queriesPrepared a10 l r
  obtain ⟨n11, hn11, rf11, h11⟩ := selectorCall_eval a11 table l.reverse r.reverse (by
    intro i
    fin_cases i <;>
      simp [a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0,
        PairPlanPreparation.queriesPrepared, PairPlanPreparation.unionPrepared,
        PairPlanPreparation.parsed, cleared, clearStacks, tableAfter, tableReset,
        moved, copied, copyStacks, activeAfter, RecordPrograms.state, ports,
        baseState, inputState, selectorStacks, SelectorPairProgram.state, table,
        SelectionTableProgram.tableBytes_eq_rawRecords])
  let a12 := selectorAfter a11 rf11 table l.reverse r.reverse
  let a13 := cleared a12 3
  let a14 := innerReset a13
  have h12 := clear_eval a12 3
  have h13 := resetInner_eval a13
  have hout : a14 = RecordPrograms.state ports
      (baseState ctx (PairScoreProgram.pairRecords
        (selectedPair ctx.seedCount ctx.processedBits.length pair :: acc)))
      false true false tail [] := by
    change callbackFinal ctx pair acc tail rf3 rf11 = _
    exact callbackFinal_eq ctx pair acc tail rf3 rf11
  have hrun := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq
    (h8.seq (h9.seq (h10.seq (h11.seq (h12.seq (h13.seq (.base (.skip a14)))))))))))))))
  rw [hout] at hrun
  refine ⟨_, ?_, by simpa only [callback, sequence] using hrun⟩
  dsimp [callbackCost]
  simp [ a12, a11, a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a0,
    cleared, clearStacks, selectorAfter, PairPlanPreparation.queriesPrepared,
    tableAfter, tableReset, moved, copied, copyStacks, activeAfter,
    PairPlanPreparation.unionPrepared, PairPlanPreparation.parsed,
    RecordPrograms.state, ports, baseState, inputState,
    ActivePlanProgram.indexRecords,
    SelectionTableProgram.unary, activeUnary_eq, l, r, table, rem, remaining]
    at hn1 hn3 hn10 hn11 ⊢
  omega

/-- The outer scan is the actual framed-record loop. It invokes the proved
pair preparation exactly once per raw pair. -/
theorem loop_eval (ctx : Context) (pairs acc : List PlanPair) (suffix : List Bool) :
    ∃ n ≤ loopCost ctx pairs,
      Eval (RecordPrograms.loop ports callback) n
        (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords acc))
          (pairs.map PairScoreProgram.pairBytes) suffix)
        (RecordPrograms.state ports
          (baseState ctx (PairScoreProgram.pairRecords
            ((selectedPairs ctx.seedCount ctx.processedBits.length pairs).reverse ++ acc)))
          false true false suffix []) := by
  induction pairs generalizing acc with
  | nil =>
      refine ⟨1, le_rfl, ?_⟩
      simpa [loopCost, selectedPairs, RecordPrograms.afterTag] using
        (Eval.while_false (test := ports.tag) (body := RecordPrograms.body ports callback)
          (a := RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
            false true false suffix []) (by simp))
  | cons pair pairs ih =>
      let tail := Encoding.encodeList id (pairs.map PairScoreProgram.pairBytes) ++ suffix
      let nextAcc := selectedPair ctx.seedCount ctx.processedBits.length pair :: acc
      have hreader : Eval (RecordPrograms.reader ports) (6 * (PairScoreProgram.pairBytes pair).length + 4)
          (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords acc))
            ((pair :: pairs).map PairScoreProgram.pairBytes) suffix)
          (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
            false true false tail (PairScoreProgram.pairBytes pair).reverse) := by
        simpa [RecordPrograms.afterTag, tail] using
          RecordPrograms.reader_eval ports (baseState ctx (PairScoreProgram.pairRecords acc))
            (PairScoreProgram.pairBytes pair) tail [] true true false
      obtain ⟨nc, hnc, hcallback⟩ := callback_eval ctx pair acc tail
      have hbranch : Eval
          (.ite ports.found (RecordPrograms.atom (.set ports.tag false))
            (RecordPrograms.atom (.pop ports.source ports.tag ports.present))) 2
          (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords nextAcc))
            false true false tail [])
          (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords nextAcc))
            (pairs.map PairScoreProgram.pairBytes) suffix) := by
        apply Eval.ite_false (by simp)
        exact RecordPrograms.pop_list_eval ports (baseState ctx (PairScoreProgram.pairRecords nextAcc))
          (pairs.map PairScoreProgram.pairBytes) suffix false true
      obtain ⟨nr, hnr, hrest⟩ := ih nextAcc
      have hbody := hreader.seq (hcallback.seq hbranch)
      have hguard : (RecordPrograms.afterTag ports (baseState ctx (PairScoreProgram.pairRecords acc))
          ((pair :: pairs).map PairScoreProgram.pairBytes) suffix).regs ports.tag = true := by
        simp [RecordPrograms.afterTag]
      have hrun := Eval.while_true hguard hbody hrest
      refine ⟨_, ?_, by simpa [RecordPrograms.loop, RecordPrograms.body, selectedPairs, nextAcc,
          List.reverse_cons, List.append_assoc] using hrun⟩
      dsimp [loopCost]
      omega

theorem iterate_eval (ctx : Context) (pairs acc : List PlanPair) (suffix : List Bool)
    (v pr f : Bool) :
    ∃ n ≤ 2 + loopCost ctx pairs,
      Eval (RecordPrograms.iterate ports callback) n
        (RecordPrograms.state ports (baseState ctx (PairScoreProgram.pairRecords acc))
          v pr f (PairScoreProgram.pairRecords pairs ++ suffix) [])
        (RecordPrograms.state ports
          (baseState ctx (PairScoreProgram.pairRecords
            ((selectedPairs ctx.seedCount ctx.processedBits.length pairs).reverse ++ acc)))
          false true false suffix []) := by
  obtain ⟨n, hn, hloop⟩ := loop_eval ctx pairs acc suffix
  have hset := RecordPrograms.set_found_eval ports
    (baseState ctx (PairScoreProgram.pairRecords acc)) v pr f false
    (PairScoreProgram.pairRecords pairs ++ suffix) []
  have hpop := RecordPrograms.pop_list_eval ports
    (baseState ctx (PairScoreProgram.pairRecords acc))
    (pairs.map PairScoreProgram.pairBytes) suffix v pr
  refine ⟨1 + (1 + n), by omega, ?_⟩
  simpa [RecordPrograms.iterate, PairScoreProgram.pairRecords, ProgramEncoding.encodeRecords]
    using hset.seq (hpop.seq hloop)

theorem command_eval (ctx : Context) (regs : Fin 16 → Bool) :
    ∃ n, n + 1 ≤ traceBound ctx ∧ Eval command n (inputState ctx regs) (outputState ctx) := by
  let a0 := inputState ctx regs
  let a1 := copied a0 31 20
  let a2 := copied a1 33 7
  let a3 := TupleProgram.pushedState 7 0 true a2
  let a4 := TupleProgram.pushedState 29 0 false a3
  let a5 : Data := ⟨fun _ => false, a4.stacks⟩
  let selected := selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs
  let a6 := RecordPrograms.state ports
    (baseState ctx (PairScoreProgram.pairRecords selected.reverse)) false true false [] []
  let a7 := cleared a6 7
  let a8 := TupleProgram.pushedState 28 0 false a7
  let a9 := PairPlanPreparation.reversed a8 29 28 (PairScoreProgram.pairRecords selected)
  let a10 := moved a9 28 29
  have h0 := copy_eval a0 31 20 (by decide) (by decide) (by decide)
    (by simp [a0, inputState])
  have h1 := copy_eval a1 33 7 (by decide) (by decide) (by decide)
    (by simp [a1, a0, copied, copyStacks, inputState])
  have h2 := TupleProgram.pushConst_eval (7 : Fin 34) (0 : Fin 16) true a2
  have h3 := TupleProgram.pushConst_eval (29 : Fin 34) (0 : Fin 16) false a3
  have h4 := resetAll_eval a4
  have ha5 : a5 = RecordPrograms.state ports
      (baseState ctx (PairScoreProgram.pairRecords [])) false false false
      (PairScoreProgram.pairRecords ctx.pairs ++ []) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp [ ports, baseState]
    · funext j
      fin_cases j <;>
        simp [ a4, a3, a2, a1, a0, copied, copyStacks,
          inputState, ports, baseState, PairScoreProgram.pairRecords,
          ProgramEncoding.encodeRecords, Encoding.encodeList]
  obtain ⟨ni, hni, hi⟩ := iterate_eval ctx ctx.pairs [] [] false false false
  have hi' : Eval (RecordPrograms.iterate ports callback) ni a5 a6 := by
    rw [ha5]
    simpa [a6, selected] using hi
  have h5 := clear_eval a6 7
  have h6 := TupleProgram.pushConst_eval (28 : Fin 34) (0 : Fin 16) false a7
  obtain ⟨nr, hnr, hr⟩ := PairPlanPreparation.reverse_eval a8 29 28 (by decide)
    (selected.map PairScoreProgram.pairBytes).reverse []
    (by simp [a8, a7, a6, cleared, clearStacks,
      RecordPrograms.state, ports, baseState, PairScoreProgram.pairRecords,
      List.map_reverse])
    (by simp [a8, a7, a6, cleared, clearStacks,
      RecordPrograms.state, ports, baseState, inputState,
      ProgramEncoding.encodeRecords, Encoding.encodeList])
    (by simp [a8, a7, a6, cleared, clearStacks,
      RecordPrograms.state, ports, baseState, inputState])
  have hr' : Eval reverseCall nr a8 a9 := by
    simpa [reverseCall, PairPlanPreparation.reverseRecords, tableRegs, reverseStacks,
      PairPlanPreparation.smallRegs, PairPlanPreparation.reversePorts,
      a9, PairScoreProgram.pairRecords] using hr
  have h7 := move_eval a9 28 29 (by decide) (by decide) (by decide)
    (by simp [a9, a8, a7, a6, PairPlanPreparation.reversed,
      cleared, clearStacks, RecordPrograms.state, ports, baseState, inputState])
  have h8 := resetAll_eval a10
  have hout : (⟨fun _ => false, a10.stacks⟩ : Data) = outputState ctx := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;>
      simp [a10, a9, a8, a7, a6, moved, copied, copyStacks, cleared, clearStacks,
        PairPlanPreparation.reversed, RecordPrograms.state,
        ports, baseState, inputState, selected]
  have hrun := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (hi'.seq (h5.seq
    (h6.seq (hr'.seq (h7.seq (h8.seq (.base (.skip _))))))))))))
  rw [hout] at hrun
  refine ⟨_, ?_, by simpa only [command, sequence] using hrun⟩
  simp [ a9, a8, a7, a6, a1, a0,
    PairPlanPreparation.reversed, copied, copyStacks,
    cleared, clearStacks, RecordPrograms.state, ports, baseState, inputState,
    traceBound, selected, PairScoreProgram.pairRecords, List.map_reverse] at hnr ⊢
  omega

/-- Full halted execution of the concrete once-per-step preparation routine.
No selected-plan table is supplied to the machine as a precomputed input. -/
theorem program_runsIn (ctx : Context) (regs : Fin 16 → Bool) :
    RunsIn program (traceBound ctx)
      ((inputState ctx regs).withPC (some program.entry))
      ((outputState ctx).withPC none) := by
  obtain ⟨n, hn, he⟩ := command_eval ctx regs
  exact ⟨n + 1, hn, by simpa [program] using compiled_halt_trace he 31 29⟩

theorem primitive_run (ctx : Context) (regs : Fin 16 → Bool) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * traceBound ctx)
      (primitiveCfg program ((inputState ctx regs).withPC (some program.entry)))
      (primitiveCfg program ((outputState ctx).withPC none)) :=
  primitive_execution program (program_runsIn ctx regs)

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
