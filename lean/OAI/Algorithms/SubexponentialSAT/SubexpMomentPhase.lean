import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentStep
import OAI.Algorithms.SubexponentialSAT.SubexpJetInitProgram
import OAI.Algorithms.SubexponentialSAT.SubexpQueryOrder

namespace OAI.Algorithms

/-!
# The fixed extraction loop

The program first creates the zero jet from the runtime dimension and word
width, then traverses the encoded extraction jobs.  The mathematical list
of cells below describes the physical packed array.  It does not provide
the runtime output or replace any of the array operations.
-/

namespace SubexponentialSAT.SubexpMomentPhase

open BitProgram StructuredCalls
open SubexpMomentProgram (Data Job outerPorts)
open SubexpMomentStep (Ready)
open SubexpSymbolicCost SymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpExtractionJobs (Query)
open SubexpDenseSerialization

abbrev loop {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Cmd 16 128 :=
  RecordPrograms.iterate outerPorts (SubexpMomentStep.command add mul loader)

abbrev command {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Cmd 16 128 :=
  .seq SubexpJetInitProgram.command (loop add mul loader)

abbrev program {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Program 16 128 (size (command add mul loader) + 1) :=
  compiled (command add mul loader) 100 102

/-- Metadata outside the job stream, current job, and output array is fixed. -/
def Framed (fixed d : Data) : Prop :=
  ∀ i : Fin 128, i ≠ 100 → i ≠ 101 → i ≠ 102 → d.stacks i = fixed.stacks i

theorem framed_refl (d : Data) : Framed d d := by
  unfold Framed
  intros
  rfl

theorem framed_recordState {fixed d : Data} (h : Framed fixed d)
    (v pr f : Bool) (src payload : List Bool) :
    Framed fixed (RecordPrograms.state outerPorts d v pr f src payload) := by
  intro i h100 h101 h102
  rw [RecordPrograms.state_stack_frame outerPorts d v pr f src payload i h100 h101]
  exact h i h100 h101 h102

theorem framed_updated {fixed d out : Data} {jet : List Bool}
    (h : Framed fixed d)
    (ho : out.stacks = Function.update (Function.update d.stacks 101 []) 102 jet) :
    Framed fixed out := by
  intro i h100 h101 h102
  rw [ho, Function.update_of_ne h102, Function.update_of_ne h101]
  exact h i h100 h101 h102

theorem ready_recordState {d : Data} {modulus width : List Bool}
    (h : Ready d modulus width) (v pr f : Bool) (src payload : List Bool) :
    Ready (RecordPrograms.state outerPorts d v pr f src payload) modulus width := by
  constructor
  · intro i
    have h100 : SubexpJetCellProgram.scalarPorts i ≠ 100 := by
      intro he; have hv := congrArg Fin.val he; change i.val = 100 at hv; omega
    have h101 : SubexpJetCellProgram.scalarPorts i ≠ 101 := by
      intro he; have hv := congrArg Fin.val he; change i.val = 101 at hv; omega
    rw [RecordPrograms.state_stack_frame outerPorts d v pr f src payload _ h100 h101]
    exact h.low i
  · intro i hi
    have h100 : i ≠ 100 := by
      intro he; subst i; simp [SubexpMomentStep.scratchPorts] at hi
    have h101 : i ≠ 101 := by
      intro he; subst i; simp [SubexpMomentStep.scratchPorts] at hi
    rw [RecordPrograms.state_stack_frame outerPorts d v pr f src payload i h100 h101]
    exact h.scratch i hi

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))
  (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D)))

local notation "ops" => preparedProgram p D M t z o
local notation "enc" => encodeFixedQuarticCoefficients p D

def job (q : Query D) : Job :=
  ⟨List.replicate q.z true, fixedKey (q.exponent, (q.u, q.z)),
    SubexpPostfixControl.serializeCode enc (source q.exponent).compile⟩

def records (qs : List (Query D)) : List (List Bool) :=
  qs.map fun q => (job p D source q).encode

def cellsBytes (cells : List (QuarticCode p D)) : List Bool :=
  (cells.map SubexpFlatAdd.encode).flatten

omit [Fact p.Prime] in
theorem cellsBytes_length (cells : List (QuarticCode p D)) :
    (cellsBytes p D cells).length = cells.length * (4 * baseWidth p (D + 1)) := by
  induction cells with
  | nil => simp [cellsBytes]
  | cons cell cells ih =>
      simp only [cellsBytes, List.map_cons, List.flatten_cons, List.length_append,
        SubexpFlatAdd.encode_length, List.length_cons] at ih ⊢
      rw [ih]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

def value (q : Query D) : QuarticCode p D :=
  SubexpCoefficientLookup.fold p (D + 1) M (fixedKey (q.exponent, (q.u, q.z)))
    (SubexpCoefficientLookup.zeroCoefficient p (D + 1))
    (SubexpMomentStep.encodedRecords
      (SubexpExecution.programEval ops slots (source q.exponent)).1)

def step (cells : List (QuarticCode p D)) (q : Query D) : List (QuarticCode p D) :=
  cells.set q.z (SubexpPreparedQuartic.binaryAdd p (D + 1) M
    (value p D M t z o slots source q)
    (cells.getD q.z (SubexpCoefficientLookup.zeroCoefficient p (D + 1)))).1

theorem step_length (cells : List (QuarticCode p D)) (q : Query D) :
    (step p D M t z o slots source cells q).length = cells.length := by
  simp only [step, List.length_set]

theorem fold_length (qs : List (Query D)) (cells : List (QuarticCode p D)) :
    (qs.foldl (step p D M t z o slots source) cells).length = cells.length := by
  induction qs generalizing cells with
  | nil => rfl
  | cons q qs ih =>
      exact (ih (step p D M t z o slots source cells q)).trans
        (step_length p D M t z o slots source cells q)

section Body

variable {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
  (loader : Program 16 128 c)
  (addBound mulBound : CoeffList D (QuarticCode p D) → CoeffList D (QuarticCode p D) → ℕ)
  (loadBound : CoeffList D (QuarticCode p D) → ℕ)
  (hslots : ∀ k ∈ slots, Retained D k)

def jobCost (q : Query D) : ℕ :=
  SubexpMomentStep.readyCost p D M t z o slots addBound mulBound loadBound
    (job p D source q) (source q.exponent)

def scheduleCost : List (Query D) → ℕ
  | [] => 0
  | q :: qs => 6 * (job p D source q).encode.length +
      jobCost p D M t z o slots source addBound mulBound loadBound q + 7 +
      scheduleCost qs

include hslots in
theorem body_eval (d : Data) (q : Query D) (cells : List (QuarticCode p D))
    (width cellWidth : List Bool) (hr : Ready d M.bits width)
    (hw : width.length = baseWidth p (D + 1))
    (hcw : cellWidth.length = 4 * baseWidth p (D + 1))
    (hc : d.stacks 104 = cellWidth) (hn : cells.length = D) (hq : q.z < D)
    (harray : d.stacks 102 = cellsBytes p D cells)
    (hjob : d.stacks 101 = (job p D source q).encode.reverse)
    (ha : SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList enc
      (fun x y => (programAdd ops slots x y).1) false add addBound
      (SubexpEvaluationProgram.contextOf
        (SubexpMomentProgram.preparedState d (job p D source q)).stacks))
    (hm : SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList enc
      (fun x y => (programMul ops slots x y).1) true mul mulBound
      (SubexpEvaluationProgram.contextOf
        (SubexpMomentProgram.preparedState d (job p D source q)).stacks))
    (hl : SubexpProjectedEvaluation.LoadImplementsGlobal enc
      (fun x => (programProject ops slots x).1) loader loadBound
      (SubexpEvaluationProgram.contextOf
        (SubexpMomentProgram.preparedState d (job p D source q)).stacks)) :
    ∃ n ≤ jobCost p D M t z o slots source addBound mulBound loadBound q,
      ∃ out : Data, Eval (SubexpMomentStep.command add mul loader) n d out ∧
        out.stacks = Function.update (Function.update d.stacks 101 []) 102
          (cellsBytes p D (step p D M t z o slots source cells q)) ∧
        Ready out M.bits width ∧ out.regs 13 = false ∧ out.regs 14 = true ∧
        out.regs 15 = false := by
  have hidx : q.z < cells.length := by simpa only [hn] using hq
  have hsplit : cells = cells.take q.z ++ cells[q.z] :: cells.drop (q.z + 1) := by
    have ht := List.take_append_drop q.z cells
    rw [List.drop_eq_getElem_cons hidx] at ht
    exact ht.symm
  have hstep : step p D M t z o slots source cells q =
      cells.take q.z ++ (SubexpPreparedQuartic.binaryAdd p (D + 1) M
        (value p D M t z o slots source q) cells[q.z]).1 :: cells.drop (q.z + 1) := by
    rw [step, List.getD_eq_getElem _ _ hidx, List.set_eq_take_append_cons_drop, ite_eq_left hidx]
  obtain ⟨n, hn', out, he, hs, hr', h13, h14, h15⟩ :=
    SubexpMomentStep.command_eval p D M t z o slots hslots add mul loader
      addBound mulBound loadBound d (job p D source q) (source q.exponent)
      width cellWidth cells[q.z] (cells.take q.z) (cells.drop (q.z + 1))
      hr hw hc hcw (by simpa only [cellsBytes, ← hsplit] using harray)
      (by simp only [job, List.length_replicate, List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)])
      hjob rfl ha hm hl
  refine ⟨n, ?_, out, he, ?_, hr', h13, h14, h15⟩
  · have hcost := SubexpMomentStep.cost_eq_readyCost p D M t z o slots
      addBound mulBound loadBound d (job p D source q) (source q.exponent) width hr
    rw [hcost] at hn'
    exact hn'
  · simpa only [cellsBytes, hstep, value, job] using hs

/-- Local trace contracts for the three installed arithmetic tables. The
metadata frame is fixed; the job stream, current payload, and jet may vary. -/
def LocalServices (fixed : Data) : Prop :=
  ∀ d : Data, Framed fixed d → ∀ q : Query D,
    SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList enc
      (fun x y => (programAdd ops slots x y).1) false add addBound
      (SubexpEvaluationProgram.contextOf
        (SubexpMomentProgram.preparedState d (job p D source q)).stacks) ∧
    SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList enc
      (fun x y => (programMul ops slots x y).1) true mul mulBound
      (SubexpEvaluationProgram.contextOf
        (SubexpMomentProgram.preparedState d (job p D source q)).stacks) ∧
    SubexpProjectedEvaluation.LoadImplementsGlobal enc
      (fun x => (programProject ops slots x).1) loader loadBound
      (SubexpEvaluationProgram.contextOf
        (SubexpMomentProgram.preparedState d (job p D source q)).stacks)

include hslots in
/-- Direct induction over the actual typed job order. The output array is
the ordered fold of the concrete binary coefficient updates. -/
theorem loop_eval (width cellWidth : List Bool)
    (hw : width.length = baseWidth p (D + 1))
    (hcw : cellWidth.length = 4 * baseWidth p (D + 1))
    (fixed : Data)
    (services : LocalServices p D M t z o slots source add mul loader
      addBound mulBound loadBound fixed)
    (suffix : List Bool) (qs : List (Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (cells : List (QuarticCode p D)) (hn : cells.length = D)
    (base : Data) (hf : Framed fixed base) (hr : Ready base M.bits width)
    (hc : base.stacks 104 = cellWidth)
    (harray : base.stacks 102 = cellsBytes p D cells) :
    ∃ n ≤ 1 + scheduleCost p D M t z o slots source addBound mulBound loadBound qs,
      ∃ out : Data,
        Eval (RecordPrograms.loop outerPorts (SubexpMomentStep.command add mul loader)) n
          (RecordPrograms.afterTag outerPorts base (records p D source qs) suffix)
          (RecordPrograms.state outerPorts out false true false suffix []) ∧
        Framed fixed out ∧ Ready out M.bits width ∧ out.stacks 104 = cellWidth ∧
        out.stacks 102 = cellsBytes p D
          (qs.foldl (step p D M t z o slots source) cells) := by
  induction qs generalizing cells base with
  | nil =>
      refine ⟨1, by simp [scheduleCost], base, ?_, hf, hr, hc, harray⟩
      apply Eval.while_false
      simp [records, RecordPrograms.afterTag]
  | cons q qs ih =>
      let tail := Encoding.encodeList id (records p D source qs) ++ suffix
      let d := RecordPrograms.state outerPorts base false true false tail
        (job p D source q).encode.reverse
      have hfd : Framed fixed d := framed_recordState hf _ _ _ _ _
      have hrd : Ready d M.bits width := ready_recordState hr _ _ _ _ _
      have hcd : d.stacks 104 = cellWidth := by
        rw [RecordPrograms.state_stack_frame outerPorts base _ _ _ _ _ 104
          (by decide) (by decide)]
        exact hc
      have had : d.stacks 102 = cellsBytes p D cells := by
        rw [RecordPrograms.state_stack_frame outerPorts base _ _ _ _ _ 102
          (by decide) (by decide)]
        exact harray
      obtain ⟨ha, hm, hl⟩ := services d hfd q
      obtain ⟨n, hn', middle, he, hs, hrm, h13, h14, h15⟩ :=
        body_eval p D M t z o slots source add mul loader addBound mulBound loadBound hslots
          d q cells width cellWidth hrd hw hcw hcd hn (valid q (by simp)) had
          (by simp [d, outerPorts, RecordPrograms.state]) ha hm hl
      have hfm : Framed fixed middle := framed_updated hfd hs
      have hcm : middle.stacks 104 = cellWidth := by
        rw [hs]
        simpa only [Function.update_of_ne (by decide : (104 : Fin 128) ≠ 102),
          Function.update_of_ne (by decide : (104 : Fin 128) ≠ 101)] using hcd
      have ham : middle.stacks 102 =
          cellsBytes p D (step p D M t z o slots source cells q) := by
        rw [hs]
        simp
      have hsource : middle.stacks 100 = tail := by
        rw [hs]
        simp [d, outerPorts, RecordPrograms.state]
      have hpayload : middle.stacks 101 = [] := by
        rw [hs]
        simp
      have hnormal : RecordPrograms.state outerPorts middle false true false tail [] = middle :=
        RecordPrograms.state_eq_self outerPorts middle _ _ _ _ _
          h13 h14 h15 hsource hpayload
      have hreader : Eval (RecordPrograms.reader outerPorts)
          (6 * (job p D source q).encode.length + 4)
          (RecordPrograms.afterTag outerPorts base (records p D source (q :: qs)) suffix) d := by
        simpa only [records, List.map_cons, RecordPrograms.afterTag, List.append_nil, tail, d] using
          RecordPrograms.reader_eval outerPorts base (job p D source q).encode tail []
            true true false
      have hbranch : Eval
          (.ite outerPorts.found (RecordPrograms.atom (.set outerPorts.tag false))
            (RecordPrograms.atom (.pop outerPorts.source outerPorts.tag outerPorts.present)))
          2 middle (RecordPrograms.afterTag outerPorts middle (records p D source qs) suffix) := by
        have hb : Eval
            (.ite outerPorts.found (RecordPrograms.atom (.set outerPorts.tag false))
              (RecordPrograms.atom (.pop outerPorts.source outerPorts.tag outerPorts.present)))
            2 (RecordPrograms.state outerPorts middle false true false tail [])
              (RecordPrograms.afterTag outerPorts middle (records p D source qs) suffix) :=
          Eval.ite_false (by simp)
            (RecordPrograms.pop_list_eval outerPorts middle (records p D source qs) suffix false true)
        simpa only [hnormal] using hb
      obtain ⟨m, hm', out, hrest, hfo, hro, hco, hao⟩ :=
        ih (fun x hx => valid x (by simp [hx]))
          (step p D M t z o slots source cells q)
          (by rw [step_length, hn]) middle hfm hrm hcm ham
      have hguard :
          (RecordPrograms.afterTag outerPorts base (records p D source (q :: qs)) suffix).regs
            outerPorts.tag = true := by
        simp [records, RecordPrograms.afterTag]
      have hrun := Eval.while_true hguard (hreader.seq (he.seq hbranch)) hrest
      refine ⟨_, ?_, out, hrun, hfo, hro, hco, hao⟩
      simp only [scheduleCost]
      omega

include hslots in
/-- The two initial iterator instructions are included in the measured
execution. All records are consumed and every job updates the physical jet. -/
theorem iterate_eval (width cellWidth : List Bool)
    (hw : width.length = baseWidth p (D + 1))
    (hcw : cellWidth.length = 4 * baseWidth p (D + 1))
    (fixed : Data)
    (services : LocalServices p D M t z o slots source add mul loader
      addBound mulBound loadBound fixed)
    (suffix : List Bool) (qs : List (Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (cells : List (QuarticCode p D)) (hn : cells.length = D)
    (base : Data) (hf : Framed fixed base) (hr : Ready base M.bits width)
    (hc : base.stacks 104 = cellWidth)
    (harray : base.stacks 102 = cellsBytes p D cells) (v pr f : Bool) :
    ∃ n ≤ 3 + scheduleCost p D M t z o slots source addBound mulBound loadBound qs,
      ∃ out : Data,
        Eval (loop add mul loader) n
          (RecordPrograms.state outerPorts base v pr f
            (Encoding.encodeList id (records p D source qs) ++ suffix) []) out ∧
        Framed fixed out ∧ Ready out M.bits width ∧ out.stacks 100 = suffix ∧
        out.stacks 101 = [] ∧ out.stacks 104 = cellWidth ∧
        out.stacks 102 = cellsBytes p D
          (qs.foldl (step p D M t z o slots source) cells) := by
  obtain ⟨n, hn', next, he, hf', hr', hc', ha'⟩ :=
    loop_eval p D M t z o slots source add mul loader addBound mulBound loadBound hslots
      width cellWidth hw hcw fixed services suffix qs valid cells hn base hf hr hc harray
  let out := RecordPrograms.state outerPorts next false true false suffix []
  have hstart := (RecordPrograms.set_found_eval outerPorts base v pr f false
    (Encoding.encodeList id (records p D source qs) ++ suffix) []).seq
      ((RecordPrograms.pop_list_eval outerPorts base (records p D source qs) suffix v pr).seq he)
  refine ⟨1 + (1 + n), by omega, out, hstart,
    framed_recordState hf' _ _ _ _ _, ready_recordState hr' _ _ _ _ _, ?_, ?_, ?_, ?_⟩
  · exact RecordPrograms.state_source _ _ _ _ _ _ _
  · exact RecordPrograms.state_payload _ _ _ _ _ _ _
  · rw [RecordPrograms.state_stack_frame outerPorts next _ _ _ _ _ 104 (by decide) (by decide)]
    exact hc'
  · rw [RecordPrograms.state_stack_frame outerPorts next _ _ _ _ _ 102 (by decide) (by decide)]
    exact ha'

end Body

def zeroCells : List (QuarticCode p D) :=
  List.replicate D (SubexpCoefficientLookup.zeroCoefficient p (D + 1))

omit [Fact p.Prime] in
theorem zeroCells_length : (zeroCells p D).length = D := by
  simp [zeroCells]

omit [Fact p.Prime] in
theorem cellsBytes_zeroCells : cellsBytes p D (zeroCells p D) =
    List.replicate (D * (4 * baseWidth p (D + 1))) false := by
  have h (n w : ℕ) : (List.replicate n (List.replicate w false)).flatten =
      List.replicate (n * w) false := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]
  simpa only [cellsBytes, zeroCells, List.map_replicate,
    SubexpCoefficientLookup.encode_zero] using h D (4 * baseWidth p (D + 1))

omit [Fact p.Prime] in
theorem ready_initialized {d : Data} {width : List Bool}
    (hr : Ready d M.bits width) :
    Ready (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) M.bits width := by
  have frame := (SubexpJetInitProgram.initialized_layout d D (baseWidth p (D + 1))).2.2
  constructor
  · intro i
    have h102 : SubexpJetCellProgram.scalarPorts i ≠ 102 := by
      intro he; have hv := congrArg Fin.val he; change i.val = 102 at hv; omega
    have h104 : SubexpJetCellProgram.scalarPorts i ≠ 104 := by
      intro he; have hv := congrArg Fin.val he; change i.val = 104 at hv; omega
    rw [frame _ h102 h104]
    exact hr.low i
  · intro i hi
    have h102 : i ≠ 102 := by
      intro he; subst i; simp [SubexpMomentStep.scratchPorts] at hi
    have h104 : i ≠ 104 := by
      intro he; subst i; simp [SubexpMomentStep.scratchPorts] at hi
    rw [frame _ h102 h104]
    exact hr.scratch i hi

omit [Fact p.Prime] in
theorem framed_initialized_cell {d out : Data}
    (h : Framed (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) out) :
    out.stacks 104 = List.replicate (4 * baseWidth p (D + 1)) false :=
  (h 104 (by decide) (by decide) (by decide)).trans
    (SubexpJetInitProgram.initialized_layout d D (baseWidth p (D + 1))).2.1

omit [Fact p.Prime] in
theorem framed_initialized_other {d out : Data}
    (h : Framed (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) out)
    (i : Fin 128) (h100 : i ≠ 100) (h101 : i ≠ 101) (h102 : i ≠ 102)
    (h104 : i ≠ 104) : out.stacks i = d.stacks i :=
  (h i h100 h101 h102).trans
    ((SubexpJetInitProgram.initialized_layout d D (baseWidth p (D + 1))).2.2 i h102 h104)

theorem generatedQueries_valid :
    ∀ q ∈ SubexpQueryOrder.generatedQueries D, (q : Query D).z < D := by
  intro q hq
  exact ((SubexpExtractionJobs.mem_queries D q).mp
    ((SubexpQueryOrder.generatedQueries_perm D).mem_iff.mp hq)).1

omit [Fact p.Prime] in
theorem records_generated : records p D source (SubexpQueryOrder.generatedQueries D) =
    (SubexpQueryOrder.generatedJobs enc source).map Job.encode := by
  simp only [records, job, SubexpQueryOrder.generatedJobs, List.map_map, Function.comp_def]

section WholePhase

variable {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
  (loader : Program 16 128 c)
  (addBound mulBound : CoeffList D (QuarticCode p D) → CoeffList D (QuarticCode p D) → ℕ)
  (loadBound : CoeffList D (QuarticCode p D) → ℕ)
  (hslots : ∀ k ∈ slots, Retained D k)

def phaseCost (qs : List (Query D)) : ℕ :=
  14 * baseWidth p (D + 1) + D * (28 * baseWidth p (D + 1) + 14) + 20 +
    scheduleCost p D M t z o slots source addBound mulBound loadBound qs

include hslots in
/-- Actual zero-array initialization followed by every extraction job. The
input supplies empty output storage, not a zero array or the final result. -/
theorem command_eval (d : Data) (width : List Bool) (qs : List (Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (hr : Ready d M.bits width) (hw : width.length = baseWidth p (D + 1))
    (hdimension : d.stacks 109 = List.replicate D true)
    (hstream : d.stacks 100 = Encoding.encodeList id (records p D source qs))
    (hpayload : d.stacks 101 = [])
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = [])
    (services : LocalServices p D M t z o slots source add mul loader
      addBound mulBound loadBound
        (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1)))) :
    ∃ n ≤ phaseCost p D M t z o slots source addBound mulBound loadBound qs,
      ∃ out : Data, Eval (command add mul loader) n d out ∧
        Framed (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) out ∧
        Ready out M.bits width ∧ out.stacks 100 = [] ∧ out.stacks 101 = [] ∧
        out.stacks 102 = cellsBytes p D
          (qs.foldl (step p D M t z o slots source) (zeroCells p D)) := by
  let initial := SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))
  let cellWidth := List.replicate (4 * baseWidth p (D + 1)) false
  have h10 : d.stacks 10 = width := by
    simpa [SubexpJetCellProgram.scalarPorts, SubexpMomentStep.lowLayout] using hr.low 10
  have hinit := SubexpJetInitProgram.command_eval d D (baseWidth p (D + 1))
    (by rw [h10, hw]) hdimension h102 h104 h106 h107 h108
  have layout := SubexpJetInitProgram.initialized_layout d D (baseWidth p (D + 1))
  have harray : initial.stacks 102 = cellsBytes p D (zeroCells p D) :=
    layout.1.trans (cellsBytes_zeroCells p D).symm
  have hcell : initial.stacks 104 = cellWidth := layout.2.1
  have hsource : initial.stacks 100 = Encoding.encodeList id (records p D source qs) :=
    (layout.2.2 100 (by decide) (by decide)).trans hstream
  have hpayload' : initial.stacks 101 = [] :=
    (layout.2.2 101 (by decide) (by decide)).trans hpayload
  obtain ⟨n, hn, out, he, hf, hr', hs, hp, _, ha⟩ :=
    iterate_eval p D M t z o slots source add mul loader addBound mulBound loadBound hslots
      width cellWidth hw (by simp [cellWidth]) initial services [] qs valid
      (zeroCells p D) (zeroCells_length p D) initial (framed_refl initial)
      (ready_initialized p D M hr) hcell harray
      (initial.regs 13) (initial.regs 14) (initial.regs 15)
  have hcanonical : RecordPrograms.state outerPorts initial
      (initial.regs 13) (initial.regs 14) (initial.regs 15)
      (Encoding.encodeList id (records p D source qs) ++ []) [] = initial :=
    RecordPrograms.state_eq_self outerPorts initial _ _ _ _ _ rfl rfl rfl
      (by simpa only [outerPorts, List.append_nil] using hsource) hpayload'
  rw [hcanonical] at he
  refine ⟨_, ?_, out, hinit.seq he, hf, hr', hs, hp, ha⟩
  dsimp only [phaseCost]
  omega

include hslots in
/-- Compilation preserves the complete initialized-loop execution with one
fixed compiler overhead for the installed finite instruction tables. -/
theorem primitive_execution (d : Data) (width : List Bool) (qs : List (Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (hr : Ready d M.bits width) (hw : width.length = baseWidth p (D + 1))
    (hdimension : d.stacks 109 = List.replicate D true)
    (hstream : d.stacks 100 = Encoding.encodeList id (records p D source qs))
    (hpayload : d.stacks 101 = [])
    (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = [])
    (services : LocalServices p D M t z o slots source add mul loader
      addBound mulBound loadBound
        (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1)))) :
    ∃ out : Data,
      Computation.RunsIn (primitive (program add mul loader)).step
        (primitiveOverhead (program add mul loader) *
          (phaseCost p D M t z o slots source addBound mulBound loadBound qs + 1))
        (primitiveCfg (program add mul loader)
          (d.withPC (some (program add mul loader).entry)))
        (primitiveCfg (program add mul loader) (out.withPC none)) ∧
      Framed (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) out ∧
      Ready out M.bits width ∧ out.stacks 100 = [] ∧ out.stacks 101 = [] ∧
      out.stacks 102 = cellsBytes p D
        (qs.foldl (step p D M t z o slots source) (zeroCells p D)) := by
  obtain ⟨n, hn, out, he, hf, hr', hs, hp, ha⟩ :=
    command_eval p D M t z o slots source add mul loader addBound mulBound loadBound hslots
      d width qs valid hr hw hdimension hstream hpayload h102 h104 h106 h107 h108 services
  have hrun : RunsIn (program add mul loader)
      (phaseCost p D M t z o slots source addBound mulBound loadBound qs + 1)
      (d.withPC (some (program add mul loader).entry)) (out.withPC none) :=
    ⟨n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 100 102⟩
  exact ⟨out, BitProgram.primitive_execution _ hrun, hf, hr', hs, hp, ha⟩

theorem scheduleCost_le (qs : List (Query D)) (bound : ℕ)
    (hbound : ∀ q ∈ qs, 6 * (job p D source q).encode.length +
      jobCost p D M t z o slots source addBound mulBound loadBound q + 7 ≤ bound) :
    scheduleCost p D M t z o slots source addBound mulBound loadBound qs ≤ bound * qs.length := by
  induction qs with
  | nil => simp [scheduleCost]
  | cons q qs ih =>
      have hh := hbound q (by simp)
      have ht := ih (fun x hx => hbound x (by simp [hx]))
      simp only [scheduleCost, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

/-- The concrete generator performs exactly the retained-moment count times
the two polynomially sized coefficient loops. -/
theorem generated_phaseCost_le (bound : ℕ)
    (hbound : ∀ q ∈ SubexpQueryOrder.generatedQueries D,
      6 * (job p D source q).encode.length +
        jobCost p D M t z o slots source addBound mulBound loadBound q + 7 ≤ bound) :
    phaseCost p D M t z o slots source addBound mulBound loadBound
        (SubexpQueryOrder.generatedQueries D) ≤
      14 * baseWidth p (D + 1) + D * (28 * baseWidth p (D + 1) + 14) + 20 +
        bound * (D * ((3 * D + 1).choose D) * (D + 1)) := by
  have h := scheduleCost_le p D M t z o slots source addBound mulBound loadBound
    (SubexpQueryOrder.generatedQueries D) bound hbound
  rw [SubexpQueryOrder.generatedQueries_length] at h
  exact Nat.add_le_add_left h _

end WholePhase

end SubexponentialSAT.SubexpMomentPhase

end OAI.Algorithms
