import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedEvaluation
import OAI.Algorithms.SubexponentialSAT.SubexpAccumulateCoefficient
import OAI.Algorithms.SubexponentialSAT.SubexpDenseSerialization

namespace OAI.Algorithms

/-!
# One complete extraction job

The fixed command below parses a job, evaluates its raw postfix source with
projection at every literal, scans the resulting coefficient records, and
adds the selected coefficient to the packed jet.  Only the installed dense
arithmetic tables retain local service contracts.  Parsing, coefficient
lookup, array update, and cleanup are concrete programs.
-/

namespace SubexponentialSAT.SubexpMomentStep

open BitProgram StructuredCalls
open SubexpMomentProgram (Job Data preparedState)
open SubexpSymbolicCost SymbolicCost
open SubexpQuarticRing SubexpLiftRing
open SubexpDenseSerialization
open SubexpPreparedEvaluation (resultState)
open SubexpJetCellProgram (scalarPorts regPorts)

/-- The coefficient scanner consumes exactly these framed-key records. -/
def encodedRecords {D : ℕ} {C : Type*} (P : CoeffList D C) : List (List Bool × C) :=
  P.map fun term => (fixedKey term.1, term.2)

private theorem flat_encode_eq_block (p D : ℕ) (a : QuarticCode p D) :
    SubexpFlatAdd.encode a = (quarticCodeBlockCode p D).block a := by
  simp [SubexpFlatAdd.encode, SubexpFlatAdd.flatten, SubexpFlatAdd.quadWords,
    quarticCodeBlockCode, recordBlockCode, wordBlockCode, quadToPair, List.append_assoc]

theorem encodedRecords_bytes (p D : ℕ) [Fact p.Prime]
    (P : CoeffList D (QuarticCode p D)) :
    Encoding.encodeList id (SubexpCoefficientLookup.encoded p (D + 1) (encodedRecords P)) =
      encodeFixedQuarticCoefficients p D P := by
  induction P with
  | nil => rfl
  | cons term P ih =>
    rcases term with ⟨a, v⟩
    change true :: (Encoding.frame (framedRecord (fixedKey a) (SubexpFlatAdd.encode v)) ++
        Encoding.encodeList id (SubexpCoefficientLookup.encoded p (D + 1) (encodedRecords P))) =
      true :: (Encoding.frame (framedRecord (fixedKey a) ((quarticCodeBlockCode p D).block v)) ++
        encodeFixedQuarticCoefficients p D P)
    rw [ih, flat_encode_eq_block]

theorem encodedRecords_coeff {D : ℕ} {C R : Type*} [Semiring R]
    (decode : C → R) (P : CoeffList D C) (a : RawIndex D) :
    ((encodedRecords P).map (fun r => if r.1 = fixedKey a then decode r.2 else 0)).sum =
      coeff (P.map fun term => (term.1, decode term.2)) a := by
  induction P with
  | nil => rfl
  | cons term P ih =>
    rcases term with ⟨b, c⟩
    have hk : fixedKey b = fixedKey a ↔ b = a := fixedKey_injective.eq_iff
    simp only [encodedRecords, List.map_cons, List.sum_cons, coeff] at ih ⊢
    simp only [hk, ih]

abbrev command {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Cmd 16 128 :=
  .seq (SubexpPreparedEvaluation.command add mul loader) SubexpAccumulateCoefficient.code

abbrev program {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
    (loader : Program 16 128 c) : Program 16 128 (size (command add mul loader) + 1) :=
  compiled (command add mul loader) 101 102

def lowLayout (modulus width source : List Bool) (i : Fin 20) : List Bool :=
  if i = 5 then modulus else if i = 10 then width else if i = 15 then source else []

theorem lookup_state_layout (regs : Fin 8 → Bool) (modulus width source : List Bool) :
    (SubexpCoefficientLookup.state regs modulus [] [] width [] source []).stacks =
      lowLayout modulus width source := by
  funext i
  fin_cases i <;> rfl

def scratchPorts : List (Fin 128) :=
  [26, 27, 28, 29, 103, 105, 110, 111, 112, 113, 114, 115, 116, 117, 118]

/-- The reusable workspace excludes the current job and the packed jet. -/
structure Ready (d : Data) (modulus width : List Bool) : Prop where
  low : ∀ i : Fin 20, d.stacks (scalarPorts i) = lowLayout modulus width [] i
  scratch : ∀ i ∈ scratchPorts, d.stacks i = []

theorem prefix_preserves (d : Data) (j : Job) (bits : List Bool) (i : Fin 128)
    (h15 : i ≠ 15) (h26 : i ≠ 26) (h27 : i ≠ 27) (h28 : i ≠ 28) (h29 : i ≠ 29)
    (h101 : i ≠ 101) (h103 : i ≠ 103) (h105 : i ≠ 105) :
    (resultState (preparedState d j) bits).stacks i = d.stacks i := by
  rw [SubexpPreparedEvaluation.resultState_preserves _ _ _ h15 h26 h27 h28 h29]
  exact SubexpMomentProgram.preparedState_preserves d j i h101 h103 h105 h26

theorem prefix_low (d : Data) (j : Job) (bits modulus width : List Bool)
    (h : Ready d modulus width) :
    ∀ i : Fin 20, (resultState (preparedState d j) bits).stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state
        ((resultState (preparedState d j) bits).regs ∘ regPorts)
        modulus [] [] width [] bits []).stacks i := by
  intro i
  rw [lookup_state_layout]
  by_cases hi : i = 15
  · subst i
    exact (SubexpPreparedEvaluation.resultState_fields _ _).1
  · have hne (n : ℕ) (hn : 20 ≤ n) (hn' : n < 128) :
        scalarPorts i ≠ (⟨n, hn'⟩ : Fin 128) := by
      intro he
      have hv := congrArg Fin.val he
      change i.val = n at hv
      omega
    have h15 : scalarPorts i ≠ 15 := by
      intro he
      apply hi
      apply Fin.ext
      exact congrArg (fun k : Fin 128 => k.val) he
    rw [prefix_preserves d j bits (scalarPorts i) h15
      (hne 26 (by omega) (by omega)) (hne 27 (by omega) (by omega))
      (hne 28 (by omega) (by omega)) (hne 29 (by omega) (by omega))
      (hne 101 (by omega) (by omega)) (hne 103 (by omega) (by omega))
      (hne 105 (by omega) (by omega)), h.low i]
    simp [lowLayout, hi]

theorem prefix_stack_equation (d : Data) (j : Job) (bits : List Bool)
    (hi : d.stacks 103 = []) (hk : d.stacks 105 = []) (hc : d.stacks 26 = []) :
    (resultState (preparedState d j) bits).stacks =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update
          d.stacks 101 []) 103 j.outputIndex.reverse) 105 j.coefficientKey.reverse)
          26 []) 27 []) 28 []) 29 []) 15 bits := by
  rw [SubexpPreparedEvaluation.resultState_stacks]
  have hp := SubexpMomentProgram.preparedState_fields d j hi hk hc
  funext i
  by_cases h101 : i = 101
  · subst i; simp [hp.1]
  by_cases h103 : i = 103
  · subst i; simp [hp.2.1]
  by_cases h105 : i = 105
  · subst i; simp [hp.2.2.1]
  by_cases h26 : i = 26
  · subst i; simp
  by_cases h27 : i = 27
  · subst i; simp
  by_cases h28 : i = 28
  · subst i; simp
  by_cases h29 : i = 29
  · subst i; simp
  by_cases h15 : i = 15
  · subst i; simp
  simp only [Function.update_of_ne h101, Function.update_of_ne h103,
    Function.update_of_ne h105, Function.update_of_ne h26, Function.update_of_ne h27,
    Function.update_of_ne h28, Function.update_of_ne h29, Function.update_of_ne h15]
  exact SubexpMomentProgram.preparedState_preserves d j i h101 h103 h105 h26

/-- All temporary ports return to their entry values.  The two net changes
are consumption of the current job and replacement of the packed jet. -/
theorem completed_stacks (d : Data) (j : Job) (bits jet modulus width : List Bool)
    (h : Ready d modulus width) :
    SubexpAccumulateCoefficient.resultStacks
        (resultState (preparedState d j) bits).stacks jet =
      Function.update (Function.update d.stacks 101 []) 102 jet := by
  have hi := h.scratch 103 (by decide)
  have hk := h.scratch 105 (by decide)
  have hc := h.scratch 26 (by decide)
  rw [prefix_stack_equation d j bits hi hk hc]
  have h8 : d.stacks 8 = [] := h.low 8
  have h14 : d.stacks 14 = [] := h.low 14
  have h15 : d.stacks 15 = [] := h.low 15
  have h27 := h.scratch 27 (by decide)
  have h28 := h.scratch 28 (by decide)
  have h29 := h.scratch 29 (by decide)
  funext i
  by_cases h101 : i = 101
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks]
  by_cases h102 : i = 102
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks]
  by_cases h103 : i = 103
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, hi]
  by_cases h105 : i = 105
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, hk]
  by_cases h26 : i = 26
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, hc]
  by_cases h27' : i = 27
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, h27]
  by_cases h28' : i = 28
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, h28]
  by_cases h29' : i = 29
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, h29]
  by_cases h8' : i = 8
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, h8]
  by_cases h14' : i = 14
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, h14]
  by_cases h15' : i = 15
  · subst i; simp [SubexpAccumulateCoefficient.resultStacks, h15]
  simp [SubexpAccumulateCoefficient.resultStacks, h101, h102, h103, h105,
    h26, h27', h28', h29', h8', h14', h15']

theorem Ready.updated {d : Data} {modulus width : List Bool} (h : Ready d modulus width)
    {e : Data} {jet : List Bool}
    (he : e.stacks = Function.update (Function.update d.stacks 101 []) 102 jet) :
    Ready e modulus width := by
  constructor
  · intro i
    rw [he]
    have h101 : scalarPorts i ≠ 101 := by
      intro eq; have hv := congrArg Fin.val eq; change i.val = 101 at hv; omega
    have h102 : scalarPorts i ≠ 102 := by
      intro eq; have hv := congrArg Fin.val eq; change i.val = 102 at hv; omega
    simpa only [Function.update_of_ne h101, Function.update_of_ne h102] using h.low i
  · intro i hi
    have h101 : i ≠ 101 := by intro heq; subst i; simp [scratchPorts] at hi
    have h102 : i ≠ 102 := by intro heq; subst i; simp [scratchPorts] at hi
    rw [he, Function.update_of_ne h102, Function.update_of_ne h101]
    exact h.scratch i hi

section Execution

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))
  (hslots : ∀ k ∈ slots, Retained D k)
  {a b c : ℕ} (add : Program 16 128 a) (mul : Program 16 128 b)
  (loader : Program 16 128 c)
  (addBound mulBound : CoeffList D (QuarticCode p D) → CoeffList D (QuarticCode p D) → ℕ)
  (loadBound : CoeffList D (QuarticCode p D) → ℕ)

local notation "ops" => preparedProgram p D M t z o
local notation "enc" => encodeFixedQuarticCoefficients p D

def cost (d : Data) (j : Job) (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) : ℕ :=
  SubexpPreparedEvaluation.executionCost ops slots enc addBound mulBound loadBound d j e +
    SubexpAccumulateCoefficient.budget (baseWidth p (D + 1)) j.outputIndex.length
      j.coefficientKey (SubexpCoefficientLookup.encoded p (D + 1)
        (encodedRecords (SubexpExecution.programEval ops slots e).1))

def readyCost (j : Job) (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) : ℕ :=
  SubexpPreparedEvaluation.preparationCost j +
    (SubexpProjectedEvaluation.operationCost (SubexpExecution.programOperations ops slots)
      enc addBound mulBound loadBound e +
      9 * (enc (SubexpExecution.programEval ops slots e).1).length + 35) +
    SubexpAccumulateCoefficient.budget (baseWidth p (D + 1)) j.outputIndex.length
      j.coefficientKey (SubexpCoefficientLookup.encoded p (D + 1)
        (encodedRecords (SubexpExecution.programEval ops slots e).1))

theorem cost_eq_readyCost (d : Data) (j : Job)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) (width : List Bool)
    (h : Ready d M.bits width) :
    cost p D M t z o slots addBound mulBound loadBound d j e =
      readyCost p D M t z o slots addBound mulBound loadBound j e := by
  have h15 : d.stacks 15 = [] := h.low 15
  have hctx : (SubexpEvaluationProgram.contextOf (preparedState d j).stacks) 11 = [] := by
    change (preparedState d j).stacks 15 = []
    rw [SubexpMomentProgram.preparedState_preserves d j 15
      (by decide) (by decide) (by decide) (by decide)]
    exact h15
  simp only [cost, readyCost, SubexpPreparedEvaluation.executionCost, hctx,
    List.length_nil, Nat.mul_zero, Nat.add_zero]

include hslots in
/-- End-to-end execution of a single well-formed extraction job.  The dense
service assumptions are local traces of fixed installed tables. -/
theorem command_eval (d : Data) (j : Job)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D)))
    (width cellWidth : List Bool) (old : QuarticCode p D)
    (earlierCells suffix : List (QuarticCode p D))
    (hready : Ready d M.bits width)
    (hwidth : width.length = baseWidth p (D + 1))
    (hcell : d.stacks 104 = cellWidth)
    (hcellWidth : cellWidth.length = 4 * baseWidth p (D + 1))
    (hjet : d.stacks 102 = ((earlierCells ++ old :: suffix).map SubexpFlatAdd.encode).flatten)
    (hindex : j.outputIndex.length = earlierCells.length)
    (hjob : d.stacks 101 = j.encode.reverse)
    (hsource : j.sourceCode = SubexpPostfixControl.serializeCode enc e.compile)
    (ha : SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList enc
      (fun x y => (programAdd ops slots x y).1) false add addBound
      (SubexpEvaluationProgram.contextOf (preparedState d j).stacks))
    (hm : SubexpProjectedEvaluation.ImplementsOnGlobal SubexpProjectedEvaluation.RetainedList enc
      (fun x y => (programMul ops slots x y).1) true mul mulBound
      (SubexpEvaluationProgram.contextOf (preparedState d j).stacks))
    (hl : SubexpProjectedEvaluation.LoadImplementsGlobal enc
      (fun x => (programProject ops slots x).1) loader loadBound
      (SubexpEvaluationProgram.contextOf (preparedState d j).stacks)) :
    let records := encodedRecords
      (SubexpExecution.programEval ops slots e).1
    let value := SubexpCoefficientLookup.fold p (D + 1) M j.coefficientKey
      (SubexpCoefficientLookup.zeroCoefficient p (D + 1)) records
    let jet := ((earlierCells ++ (SubexpPreparedQuartic.binaryAdd p (D + 1) M value old).1 ::
      suffix).map SubexpFlatAdd.encode).flatten
    ∃ n ≤ cost p D M t z o slots addBound mulBound loadBound d j e,
      ∃ out : Data, Eval (command add mul loader) n d out ∧
        out.stacks = Function.update (Function.update d.stacks 101 []) 102 jet ∧
        Ready out M.bits width ∧ out.regs 13 = false ∧ out.regs 14 = true ∧
        out.regs 15 = false := by
  dsimp only
  let bits := enc (SubexpExecution.programEval ops slots e).1
  let mid := resultState (preparedState d j) bits
  let records := encodedRecords (SubexpExecution.programEval ops slots e).1
  obtain ⟨n, hn, hrun⟩ := SubexpPreparedEvaluation.command_runs ops slots hslots
    add mul loader enc addBound mulBound loadBound d j e hsource hjob
    (hready.scratch 103 (by decide)) (hready.scratch 105 (by decide))
    (hready.scratch 26 (by decide)) (hready.scratch 110 (by decide))
    (hready.scratch 111 (by decide)) (hready.scratch 27 (by decide))
    (hready.scratch 28 (by decide)) (hready.scratch 29 (by decide)) ha hm hl
  have hf := SubexpPreparedEvaluation.output_layout d j bits
    (hready.scratch 103 (by decide)) (hready.scratch 105 (by decide))
    (hready.scratch 26 (by decide))
  have hp (i : Fin 128) (hi : i ∈ [104, 112, 113, 114, 115, 116, 117, 118]) :
      mid.stacks i = d.stacks i := by
    have hne : i ≠ 15 ∧ i ≠ 26 ∧ i ≠ 27 ∧ i ≠ 28 ∧ i ≠ 29 ∧
        i ≠ 101 ∧ i ≠ 103 ∧ i ≠ 105 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact prefix_preserves d j bits i hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1
      hne.2.2.2.2.1 hne.2.2.2.2.2.1 hne.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2
  have hsmall : ∀ i : Fin 20, mid.stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state (mid.regs ∘ regPorts) M.bits [] [] width []
        (Encoding.encodeList id (SubexpCoefficientLookup.encoded p (D + 1) records)) []).stacks i := by
    change ∀ i : Fin 20, mid.stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state (mid.regs ∘ regPorts) M.bits [] [] width []
        (Encoding.encodeList id (SubexpCoefficientLookup.encoded p (D + 1)
          (encodedRecords
            (SubexpExecution.programEval ops slots e).1))) []).stacks i
    rw [encodedRecords_bytes]
    exact prefix_low d j bits M.bits width hready
  obtain ⟨m, hm', out, hout, hst, hr13, hr14, hr15⟩ :=
    SubexpAccumulateCoefficient.accumulate_eval p (D + 1) M mid records
      j.coefficientKey old earlierCells suffix j.outputIndex.reverse cellWidth width
      hf.2.2.1 (hf.2.2.2.2.2.trans hjet) hf.2.1
      (by simpa only [List.length_reverse] using hindex)
      ((hp 104 (by simp)).trans hcell) hcellWidth hwidth hsmall
      ((hp 112 (by simp)).trans (hready.scratch 112 (by decide)))
      ((hp 113 (by simp)).trans (hready.scratch 113 (by decide)))
      ((hp 114 (by simp)).trans (hready.scratch 114 (by decide)))
      ((hp 115 (by simp)).trans (hready.scratch 115 (by decide)))
      ((hp 116 (by simp)).trans (hready.scratch 116 (by decide)))
      ((hp 117 (by simp)).trans (hready.scratch 117 (by decide)))
      ((hp 118 (by simp)).trans (hready.scratch 118 (by decide)))
  have hnet := hst.trans (completed_stacks d j bits _ M.bits width hready)
  refine ⟨n + m, ?_, out, Eval.seq hrun hout, hnet, hready.updated hnet,
    hr13, hr14, hr15⟩
  simpa only [cost, List.length_reverse] using Nat.add_le_add hn hm'

end Execution

theorem program_trace {a b c n : ℕ} (add : Program 16 128 a)
    (mul : Program 16 128 b) (loader : Program 16 128 c) {before after : Data}
    (h : Eval (command add mul loader) n before after) :
    Trace (program add mul loader) (n + 1)
      (before.withPC (some (program add mul loader).entry)) (after.withPC none) :=
  compiled_halt_trace h 101 102

/-- The exact coefficient stored by the concrete update has the expected
ring value, including sums of duplicate matching records. -/
theorem updated_quotient (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (c : Fin 4 → ZMod (p ^ (D + 1)))
    (P : CoeffList D (QuarticCode p D)) (a : RawIndex D) (old : QuarticCode p D) :
    quotientDenote c
        (((SubexpPreparedQuartic.binaryAdd p (D + 1) M
          (SubexpCoefficientLookup.fold p (D + 1) M (fixedKey a)
            (SubexpCoefficientLookup.zeroCoefficient p (D + 1))
            (encodedRecords P)) old).1).map
          (wordValue p (D + 1))) =
      quotientDenote c (old.map (wordValue p (D + 1))) +
        coeff (P.map (fun term => (term.1,
          quotientDenote c (term.2.map (wordValue p (D + 1)))))) a := by
  rw [SubexpAccumulateCoefficient.accumulated_quotient]
  exact congrArg (fun x => quotientDenote c (old.map (wordValue p (D + 1))) + x)
    (encodedRecords_coeff (fun q : QuarticCode p D =>
      quotientDenote c (q.map (wordValue p (D + 1)))) P a)

end SubexponentialSAT.SubexpMomentStep

end OAI.Algorithms
