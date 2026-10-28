import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchFraming
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchLoopCode
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchState
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchBoundary
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorageBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixFor
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# The actual outer local-basis record loops

The callback premise is an actual bounded evaluation of one fixed color
program with its full stack frame. The two unary loops, record framing,
reversal, and cleanup below are concrete instructions. No final batch
execution or precomputed batch output is assumed.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls
open ProgramEncoding (encodeRecords)

def ColorStep (body : Code) (ctx : Context) (width : Word) (r Q : ℕ)
    (Good : ℕ → ℕ → Word → Prop) (C : ℕ) : Prop :=
  ∀ t, t < Q → ∀ g, g < r →
    ∀ outerAcc innerAcc outerFuel innerFuel regs,
      ∃ n result finalRegs, n ≤ C ∧ Good t g result ∧
        Eval body n
          (boundaryState ctx width t g outerAcc innerAcc outerFuel innerFuel regs)
          (boundaryState ctx width t (g + 1) outerAcc
            ((true :: Encoding.frame result).reverse ++ innerAcc)
            outerFuel innerFuel finalRegs)

/-- Forward record bytes without the final list terminator. -/
def recordPrefix (records : List Word) : Word :=
  records.flatMap (fun word => true :: Encoding.frame word)

def recordAccumulator (records : List Word) : Word := (recordPrefix records).reverse

@[simp] theorem recordAccumulator_nil : recordAccumulator [] = [] := rfl

theorem recordAccumulator_snoc (records : List Word) (word : Word) :
    recordAccumulator (records ++ [word]) =
      (true :: Encoding.frame word).reverse ++ recordAccumulator records := by
  simp [recordAccumulator, recordPrefix, List.flatMap_append, List.reverse_append]

theorem encodeRecords_eq_prefix (records : List Word) :
    encodeRecords records = recordPrefix records ++ [false] := by
  induction records with
  | nil => rfl
  | cons word words ih =>
      change (true :: Encoding.frame word) ++ encodeRecords words =
        ((true :: Encoding.frame word) ++ recordPrefix words) ++ [false]
      rw [ih, List.append_assoc]

theorem recordAccumulator_finished (records : List Word) :
    (false :: recordAccumulator records).reverse = encodeRecords records := by
  simp [recordAccumulator, List.reverse_cons, encodeRecords_eq_prefix]

theorem recordAccumulator_reverse_suffix (records : List Word) :
    (recordAccumulator records).reverse ++ [false] = encodeRecords records := by
  simpa only [List.reverse_cons] using recordAccumulator_finished records

theorem encodeRecords_length_accumulator (records : List Word) :
    (encodeRecords records).length = (recordAccumulator records).length + 1 := by
  rw [← recordAccumulator_finished]
  simp

private theorem boundary_inner_frame (ctx : Context) (width : Word) (t g : ℕ)
    (oa ia ofuel ifuel ifuel' : Word) (regs regs' : Fin 32 → Bool)
    (j : Fin 128) (hj : j ≠ 120) :
    (boundaryState ctx width t g oa ia ofuel ifuel regs).stacks j =
      (boundaryState ctx width t g oa ia ofuel ifuel' regs').stacks j := by
  simp [boundaryState, outputState, inputState, hj]

private theorem boundary_outer_frame (ctx : Context) (width : Word) (t g : ℕ)
    (oa ia ofuel ofuel' ifuel : Word) (regs regs' : Fin 32 → Bool)
    (j : Fin 128) (hj : j ≠ 119) :
    (boundaryState ctx width t g oa ia ofuel ifuel regs).stacks j =
      (boundaryState ctx width t g oa ia ofuel' ifuel regs').stacks j := by
  simp [boundaryState, outputState, inputState, hj]

def ColorInvariant (ctx : Context) (width : Word) (t : ℕ)
    (oa ofuel : Word) (Good : ℕ → ℕ → Word → Prop) (g : ℕ) (d : Data) : Prop :=
  ∃ records, List.Forall₂ (Good t) (List.range g) records ∧
    d.stacks = (boundaryState ctx width t g oa (recordAccumulator records)
      ofuel (d.stacks 120) d.regs).stacks

theorem colorInvariant_stable (ctx : Context) (width : Word) (t : ℕ)
    (oa ofuel : Word) (Good : ℕ → ℕ → Word → Prop) :
    UnaryForPrograms.FrameStable colorLoopPorts (ColorInvariant ctx width t oa ofuel Good) := by
  intro g d e hframe hi
  obtain ⟨records, hrecords, hs⟩ := hi
  refine ⟨records, hrecords, ?_⟩
  funext j
  by_cases hj : j = 120
  · subst j
    simp [boundaryState]
  · exact (hframe j hj).symm.trans ((congrFun hs j).trans
      (boundary_inner_frame ctx width t g oa (recordAccumulator records)
        ofuel (d.stacks 120) (e.stacks 120) d.regs e.regs j hj))

theorem colorInvariant_step (body : Code) (ctx : Context) (width : Word)
    (r Q C t : ℕ) (Good : ℕ → ℕ → Word → Prop)
    (hbody : ColorStep body ctx width r Q Good C) (ht : t < Q) (oa ofuel : Word) :
    ConstraintMatrixFor.BodyStep colorLoopPorts body r
      (ColorInvariant ctx width t oa ofuel Good) (fun _ => C) := by
  intro g hg d hi
  obtain ⟨records, hrecords, hs⟩ := hi
  have hd : d = boundaryState ctx width t g oa (recordAccumulator records)
      ofuel (d.stacks 120) d.regs := by
    exact SubexpScanPrimitives.state_ext rfl hs
  obtain ⟨n, result, regs, hn, hresult, he⟩ :=
    hbody t ht g hg oa (recordAccumulator records) ofuel (d.stacks 120) d.regs
  let e := boundaryState ctx width t (g + 1) oa
    ((true :: Encoding.frame result).reverse ++ recordAccumulator records)
    ofuel (d.stacks 120) regs
  refine ⟨n, e, hn, ?_, ?_, records ++ [result], ?_, ?_⟩
  · rw [← hd] at he
    exact he
  · simp [e, colorLoopPorts, boundaryState]
  · rw [List.range_succ]
    exact List.rel_append hrecords (.cons hresult .nil)
  · simp [e, recordAccumulator_snoc, boundaryState]

def colorLoopCost (r C : ℕ) : ℕ := r * (C + 2) + 2
def positionCost (r C : ℕ) : ℕ := 18 * colorLoopCost r C + 9 * r + 51
def positionLoopCost (r Q C : ℕ) : ℕ := Q * (positionCost r C + 2) + 2
def coreCost (r Q C : ℕ) : ℕ := 4 * positionLoopCost r Q C + 9 * Q + 16

theorem colorLoop_eval (body : Code) (ctx : Context) (width : Word)
    (r Q C t : ℕ) (Good : ℕ → ℕ → Word → Prop)
    (hbody : ColorStep body ctx width r Q Good C) (ht : t < Q)
    (hr : ctx.colors.length = r) (oa ofuel : Word) (regs : Fin 32 → Bool) :
    ∃ n records finalRegs, n ≤ colorLoopCost r C ∧
      List.Forall₂ (Good t) (List.range r) records ∧
      Eval (UnaryForPrograms.forCmd colorLoopPorts body) n
        (boundaryState ctx width t 0 oa [] ofuel ctx.colors regs)
        (boundaryState ctx width t r oa (recordAccumulator records) ofuel [] finalRegs) := by
  let d := boundaryState ctx width t 0 oa [] ofuel ctx.colors regs
  have hi : ColorInvariant ctx width t oa ofuel Good 0 d := by
    refine ⟨[], .nil, ?_⟩
    simp [d, boundaryState, recordAccumulator, recordPrefix]
  have hc : (d.stacks colorLoopPorts.counter).length = r := by
    simpa [d, colorLoopPorts, boundaryState] using hr
  obtain ⟨n, hn, e, he, hei, hempty⟩ := ConstraintMatrixFor.for_correct_constant
    colorLoopPorts body r C (ColorInvariant ctx width t oa ofuel Good)
    (colorInvariant_stable ctx width t oa ofuel Good)
    (colorInvariant_step body ctx width r Q C t Good hbody ht oa ofuel) d hc hi
  obtain ⟨records, hrecords, hs⟩ := hei
  have heq : e = boundaryState ctx width t r oa (recordAccumulator records) ofuel [] e.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    simpa only [show e.stacks 120 = [] from hempty] using hs
  rw [heq] at he
  exact ⟨n, records, e.regs, hn, hrecords, he⟩

theorem finishColorList_eval (ctx : Context) (width : Word) (t g : ℕ)
    (oa ofuel ifuel : Word) (records : List Word) (regs : Fin 32 → Bool) :
    ∃ finalRegs, Eval finishColorList (17 * (encodeRecords records).length + 24)
      (boundaryState ctx width t g oa (recordAccumulator records) ofuel ifuel regs)
      (boundaryState ctx width t g
        ((true :: Encoding.frame (encodeRecords records)).reverse ++ oa)
        [] ofuel ifuel finalRegs) := by
  let a := boundaryState ctx width t g oa (recordAccumulator records) ofuel ifuel regs
  let b := TupleProgram.pushedState 122 0 false a
  let c := transferState 122 126 b
  let e := recordedState 126 121 c
  have hp := TupleProgram.pushConst_eval (122 : Fin 128) (0 : Fin 32) false a
  have ht := transfer_eval 122 126 b (by decide)
  have hc0 : c.stacks 0 = [] := by
    simp [c, b, a, transferState, StackRoutines.transferStacks,
      boundaryState, outputState, inputState]
  have hc125 : c.stacks 125 = [] := by
    simp [c, b, a, transferState, StackRoutines.transferStacks,
      boundaryState, outputState, inputState]
  have hr := appendRecord_eval 126 121 c (by decide) (by decide) (by decide)
    (by decide) hc0 hc125
  have hb122 : b.stacks 122 = false :: recordAccumulator records := by
    simp [b, a, boundaryState]
  have hc126 : c.stacks 126 = encodeRecords records := by
    simp [c, transferState, StackRoutines.transferStacks, b, a,
      boundaryState, outputState, inputState,
      recordAccumulator_reverse_suffix]
  have heq : e = boundaryState ctx width t g
      ((true :: Encoding.frame (encodeRecords records)).reverse ++ oa)
      [] ofuel ifuel e.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext j
    by_cases h121 : j = 121 <;> by_cases h122 : j = 122 <;> by_cases h126 : j = 126 <;>
      simp [e, c, b, a, recordedState, transferState, StackRoutines.transferStacks,
        boundaryState, outputState, inputState,
        recordAccumulator_reverse_suffix, h121, h122, h126]
  rw [hc126] at hr
  have hl : (b.stacks 122).length = (encodeRecords records).length := by
    rw [hb122, encodeRecords_length_accumulator]
    simp
  rw [hl] at ht
  refine ⟨e.regs, ?_⟩
  have he := hp.seq (ht.seq hr)
  change Eval finishColorList _ a e at he
  rw [heq] at he
  convert he using 1 ; omega

theorem advancePosition_eval (ctx : Context) (width : Word) (t g : ℕ)
    (oa ofuel ifuel : Word) (regs : Fin 32 → Bool) :
    ∃ finalRegs, Eval (.seq (clear 118) (TupleProgram.pushConst 117 0 true)) (2 * g + 5)
      (boundaryState ctx width t g oa [] ofuel ifuel regs)
      (boundaryState ctx width (t + 1) 0 oa [] ofuel ifuel finalRegs) := by
  let a := boundaryState ctx width t g oa [] ofuel ifuel regs
  let b := clearState 118 a
  let e := TupleProgram.pushedState 117 0 true b
  have hc := clear_eval 118 a
  have hp := TupleProgram.pushConst_eval (117 : Fin 128) (0 : Fin 32) true b
  have hl : (a.stacks 118).length = g := by simp [a, boundaryState]
  rw [hl] at hc
  have heq : e = boundaryState ctx width (t + 1) 0 oa [] ofuel ifuel e.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext j
    by_cases h117 : j = 117 <;> by_cases h118 : j = 118 <;>
      simp [e, b, a, clearState, StackRoutines.clearStacks,
        boundaryState, outputState, inputState, List.replicate_succ, h117, h118]
  refine ⟨e.regs, ?_⟩
  have he := hc.seq hp
  change Eval (.seq (clear 118) (TupleProgram.pushConst 117 0 true)) _ a e at he
  rw [heq] at he
  exact he

theorem batchPositionBody_eval (body : Code) (ctx : Context) (width : Word)
    (r Q C t : ℕ) (Good : ℕ → ℕ → Word → Prop)
    (hbody : ColorStep body ctx width r Q Good C) (ht : t < Q)
    (hr : ctx.colors.length = r) (oa ofuel : Word) (regs : Fin 32 → Bool) :
    ∃ n records finalRegs, n ≤ positionCost r C ∧
      List.Forall₂ (Good t) (List.range r) records ∧
      Eval (batchPositionBody body) n
        (boundaryState ctx width t 0 oa [] ofuel [] regs)
        (boundaryState ctx width (t + 1) 0
          ((true :: Encoding.frame (encodeRecords records)).reverse ++ oa)
          [] ofuel [] finalRegs) := by
  let a := boundaryState ctx width t 0 oa [] ofuel [] regs
  let b := copyState 112 120 a
  have h125 : a.stacks 125 = [] := by simp [a, boundaryState, outputState, inputState]
  have hc := copy_eval 112 120 a (by decide) (by decide) (by decide) h125
  have hl : (a.stacks 112).length = r := by
    simpa [a, boundaryState, outputState, inputState] using hr
  rw [hl] at hc
  have hb : b = boundaryState ctx width t 0 oa [] ofuel ctx.colors b.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext j
    by_cases hj : j = 120 <;>
      simp [b, a, copyState, StackRoutines.copyStacks, boundaryState, outputState, inputState, hj]
  obtain ⟨n, records, middleRegs, hn, hg, hi⟩ :=
    colorLoop_eval body ctx width r Q C t Good hbody ht hr oa ofuel b.regs
  have hlen : (recordAccumulator records).length ≤ n := by
    simpa [boundaryState] using eval_stack_length_le hi (122 : Fin 128)
  obtain ⟨finishRegs, hf⟩ := finishColorList_eval ctx width t r oa ofuel [] records middleRegs
  obtain ⟨finalRegs, ha⟩ := advancePosition_eval ctx width t r
    ((true :: Encoding.frame (encodeRecords records)).reverse ++ oa) ofuel [] finishRegs
  change Eval (copy 112 120) (7 * r + 5) a b at hc
  rw [hb] at hc
  refine ⟨(7 * r + 5) + (n + ((17 * (encodeRecords records).length + 24) + (2 * r + 5))),
    records, finalRegs, ?_, hg, ?_⟩
  · rw [encodeRecords_length_accumulator]
    unfold positionCost
    omega
  · exact hc.seq (hi.seq (hf.seq ha))

def RowsGood (Good : ℕ → ℕ → Word → Prop) (r t : ℕ) (rows : List (List Word)) : Prop :=
  List.Forall₂ (fun i row => List.Forall₂ (Good i) (List.range r) row) (List.range t) rows

def PositionInvariant (ctx : Context) (width : Word) (r : ℕ)
    (Good : ℕ → ℕ → Word → Prop) (t : ℕ) (d : Data) : Prop :=
  ∃ rows, RowsGood Good r t rows ∧
    d.stacks = (boundaryState ctx width t 0
      (recordAccumulator (rows.map encodeRecords)) [] (d.stacks 119) [] d.regs).stacks

theorem positionInvariant_stable (ctx : Context) (width : Word) (r : ℕ)
    (Good : ℕ → ℕ → Word → Prop) :
    UnaryForPrograms.FrameStable positionLoopPorts (PositionInvariant ctx width r Good) := by
  intro t d e hframe hi
  obtain ⟨rows, hrows, hs⟩ := hi
  refine ⟨rows, hrows, ?_⟩
  funext j
  by_cases hj : j = 119
  · subst j
    simp [boundaryState]
  · exact (hframe j hj).symm.trans ((congrFun hs j).trans
      (boundary_outer_frame ctx width t 0 (recordAccumulator (rows.map encodeRecords)) []
        (d.stacks 119) (e.stacks 119) [] d.regs e.regs j hj))

theorem positionInvariant_step (body : Code) (ctx : Context) (width : Word)
    (r Q C : ℕ) (Good : ℕ → ℕ → Word → Prop)
    (hbody : ColorStep body ctx width r Q Good C) (hr : ctx.colors.length = r) :
    ConstraintMatrixFor.BodyStep positionLoopPorts (batchPositionBody body) Q
      (PositionInvariant ctx width r Good) (fun _ => positionCost r C) := by
  intro t ht d hi
  obtain ⟨rows, hrows, hs⟩ := hi
  have hd : d = boundaryState ctx width t 0 (recordAccumulator (rows.map encodeRecords))
      [] (d.stacks 119) [] d.regs := SubexpScanPrimitives.state_ext rfl hs
  obtain ⟨n, records, regs, hn, hg, he⟩ := batchPositionBody_eval body ctx width r Q C t
    Good hbody ht hr (recordAccumulator (rows.map encodeRecords)) (d.stacks 119) d.regs
  let e := boundaryState ctx width (t + 1) 0
    ((true :: Encoding.frame (encodeRecords records)).reverse ++ recordAccumulator (rows.map encodeRecords))
    [] (d.stacks 119) [] regs
  refine ⟨n, e, hn, ?_, ?_, rows ++ [records], ?_, ?_⟩
  · rw [← hd] at he
    exact he
  · simp [e, positionLoopPorts, boundaryState]
  · unfold RowsGood at hrows ⊢
    rw [List.range_succ]
    exact List.rel_append hrows (.cons hg .nil)
  · simp [e, List.map_append, recordAccumulator_snoc, boundaryState]

theorem positionLoop_eval (body : Code) (ctx : Context) (width : Word)
    (r Q C : ℕ) (Good : ℕ → ℕ → Word → Prop)
    (hbody : ColorStep body ctx width r Q Good C)
    (hr : ctx.colors.length = r) (hQ : ctx.positions.length = Q) (regs : Fin 32 → Bool) :
    ∃ n rows finalRegs, n ≤ positionLoopCost r Q C ∧ RowsGood Good r Q rows ∧
      Eval (UnaryForPrograms.forCmd positionLoopPorts (batchPositionBody body)) n
        (boundaryState ctx width 0 0 [] [] ctx.positions [] regs)
        (boundaryState ctx width Q 0 (recordAccumulator (rows.map encodeRecords)) [] [] [] finalRegs) := by
  let d := boundaryState ctx width 0 0 [] [] ctx.positions [] regs
  have hi : PositionInvariant ctx width r Good 0 d := by
    refine ⟨[], .nil, ?_⟩
    simp [d, boundaryState, recordAccumulator, recordPrefix]
  have hc : (d.stacks positionLoopPorts.counter).length = Q := by
    simpa [d, positionLoopPorts, boundaryState] using hQ
  obtain ⟨n, hn, e, he, hei, hempty⟩ := ConstraintMatrixFor.for_correct_constant
    positionLoopPorts (batchPositionBody body) Q (positionCost r C)
    (PositionInvariant ctx width r Good) (positionInvariant_stable ctx width r Good)
    (positionInvariant_step body ctx width r Q C Good hbody hr) d hc hi
  obtain ⟨rows, hrows, hs⟩ := hei
  have heq : e = boundaryState ctx width Q 0 (recordAccumulator (rows.map encodeRecords))
      [] [] [] e.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    simpa only [show e.stacks 119 = [] from hempty] using hs
  rw [heq] at he
  exact ⟨n, rows, e.regs, hn, hrows, he⟩

def finishBatch : Code := .seq (TupleProgram.pushConst 121 0 false)
  (.seq (transfer 121 127) (clear 117))

theorem finishBatch_eval (ctx : Context) (width : Word) (Q : ℕ)
    (records : List Word) (regs : Fin 32 → Bool) :
    ∃ finalRegs, Eval finishBatch (3 * (encodeRecords records).length + 2 * Q + 8)
      (boundaryState ctx width Q 0 (recordAccumulator records) [] [] [] regs)
      (outputState ctx width (encodeRecords records) finalRegs) := by
  let a := boundaryState ctx width Q 0 (recordAccumulator records) [] [] [] regs
  let b := TupleProgram.pushedState 121 0 false a
  let c := transferState 121 127 b
  let e := clearState 117 c
  have hp := TupleProgram.pushConst_eval (121 : Fin 128) (0 : Fin 32) false a
  have ht := transfer_eval 121 127 b (by decide)
  have hc := clear_eval 117 c
  have hb121 : b.stacks 121 = false :: recordAccumulator records := by
    simp [b, a, boundaryState]
  have hl : (b.stacks 121).length = (encodeRecords records).length := by
    rw [hb121, encodeRecords_length_accumulator]
    simp
  have hc117 : (c.stacks 117).length = Q := by
    simp [c, b, a, transferState, StackRoutines.transferStacks,
      boundaryState]
  rw [hl] at ht
  rw [hc117] at hc
  have heq : e = outputState ctx width (encodeRecords records) e.regs := by
    clear hp ht hc hb121 hl hc117
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext j
    by_cases h117 : j = 117
    · subst j
      simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix]
    by_cases h118 : j = 118
    · subst j
      simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix]
    by_cases h119 : j = 119
    · subst j
      simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix]
    by_cases h120 : j = 120
    · subst j
      simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix]
    by_cases h121 : j = 121
    · subst j
      simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix]
    by_cases h122 : j = 122
    · subst j
      simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix]
    by_cases h127 : j = 127
    · subst j
      simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix]
    simp [e, c, b, a, clearState, StackRoutines.clearStacks, transferState,
        StackRoutines.transferStacks, boundaryState,
        outputState, inputState, recordAccumulator_reverse_suffix,
        h117, h118, h119, h120, h121, h122, h127]
  refine ⟨e.regs, ?_⟩
  have he := hp.seq (ht.seq hc)
  change Eval finishBatch _ a e at he
  rw [heq] at he
  convert he using 1 ; omega

/-- Every output row is in increasing position/color order. The size of
the actual accumulated words is charged using growth along actual traces. -/
theorem batchCore_eval (body : Code) (ctx : Context) (width : Word)
    (r Q C : ℕ) (Good : ℕ → ℕ → Word → Prop)
    (hbody : ColorStep body ctx width r Q Good C)
    (hr : ctx.colors.length = r) (hQ : ctx.positions.length = Q) (regs : Fin 32 → Bool) :
    ∃ n rows finalRegs, n ≤ coreCost r Q C ∧ RowsGood Good r Q rows ∧
      Eval (batchCore body) n
        (boundaryState ctx width 0 0 [] [] [] [] regs)
        (outputState ctx width (encodeRecords (rows.map encodeRecords)) finalRegs) := by
  let a := boundaryState ctx width 0 0 [] [] [] [] regs
  let b := copyState 113 119 a
  have h125 : a.stacks 125 = [] := by simp [a, boundaryState, outputState, inputState]
  have hc := copy_eval 113 119 a (by decide) (by decide) (by decide) h125
  have hl : (a.stacks 113).length = Q := by
    simpa [a, boundaryState, outputState, inputState] using hQ
  rw [hl] at hc
  have hb : b = boundaryState ctx width 0 0 [] [] ctx.positions [] b.regs := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    funext j
    by_cases hj : j = 119 <;>
      simp [b, a, copyState, StackRoutines.copyStacks, boundaryState, outputState, inputState, hj]
  obtain ⟨n, rows, middleRegs, hn, hg, hi⟩ :=
    positionLoop_eval body ctx width r Q C Good hbody hr hQ b.regs
  have hlen : (recordAccumulator (rows.map encodeRecords)).length ≤ n := by
    simpa [boundaryState] using eval_stack_length_le hi (121 : Fin 128)
  obtain ⟨finalRegs, hf⟩ := finishBatch_eval ctx width Q (rows.map encodeRecords) middleRegs
  change Eval (copy 113 119) (7 * Q + 5) a b at hc
  rw [hb] at hc
  refine ⟨(7 * Q + 5) + (n + (3 * (encodeRecords (rows.map encodeRecords)).length + 2 * Q + 8)),
    rows, finalRegs, ?_, hg, ?_⟩
  · rw [encodeRecords_length_accumulator]
    unfold coreCost
    omega
  · exact hc.seq (hi.seq hf)

def batchCoreProgram (body : Code) := compiled (batchCore body) 107 127

theorem batchCore_program_runs (body : Code) (ctx : Context) (width : Word)
    (r Q C : ℕ) (Good : ℕ → ℕ → Word → Prop)
    (hbody : ColorStep body ctx width r Q Good C)
    (hr : ctx.colors.length = r) (hQ : ctx.positions.length = Q) (regs : Fin 32 → Bool) :
    ∃ rows finalRegs, RowsGood Good r Q rows ∧
      RunsIn (batchCoreProgram body) (coreCost r Q C + 1)
        ((boundaryState ctx width 0 0 [] [] [] [] regs).withPC (some (batchCoreProgram body).entry))
        ((outputState ctx width (encodeRecords (rows.map encodeRecords)) finalRegs).withPC none) := by
  obtain ⟨n, rows, rf, hn, hg, he⟩ := batchCore_eval body ctx width r Q C Good hbody hr hQ regs
  exact ⟨rows, rf, hg, n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 107 127⟩

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
