import OAI.Algorithms.SubexponentialSAT.SqrtLog.BinaryArgminBootstrap
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramLoop
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedy
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.ModularPrograms
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

/-- The original numerical comparator and strict update, with a concrete halt. -/
def updateProgram := compiled BinaryArgmin.update 8 2

/-- A single local update has polynomial space at every instruction prefix.
The bound includes the untouched iterator/caller frame on port 8. -/
theorem update_trace_space (B C : ℕ) (next best : BinaryArgmin.Entry)
    (frame : List Bool) (regs : Fin 8 → Bool)
    (hn : next.score.length = B) (hb : best.score.length = B)
    (hcn : next.payload.length ≤ C) (hcb : best.payload.length ≤ C) :
    ∃ steps ≤ 100 * (B + C + 1) + 1, ∃ regs',
      Trace updateProgram steps
        ((BinaryArgmin.data regs next best frame).withPC (some updateProgram.entry))
        ((BinaryArgmin.data regs' BinaryArgmin.empty (BinaryArgmin.pick best next)
          frame).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace updateProgram prefixSteps
          ((BinaryArgmin.data regs next best frame).withPC (some updateProgram.entry))
          intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          9 * (B + C + frame.length) + 100 * (B + C + 1) + 1 := by
  obtain ⟨steps, hsteps, regs', ht⟩ :=
    BinaryArgmin.update_eval B C next best frame regs hn hb hcn hcb
  refine ⟨steps + 1, by omega, regs', compiled_halt_trace ht 8 2, ?_⟩
  intro prefixSteps intermediate hp htrace i
  have hinitial : dataBits
      ((BinaryArgmin.data regs next best frame).withPC (some updateProgram.entry)) ≤
        9 * (B + C + frame.length) := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _j : Fin 9, (B + C + frame.length) := by
        apply Finset.sum_le_sum
        intro j _
        fin_cases j <;> simp [BinaryArgmin.data, BinaryArgmin.store] <;> omega
      _ = _ := by simp
  have hsize := trace_dataBits updateProgram htrace
  have hport : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  omega


/-- Bootstrap from the separately paid first score. -/
def installProgram := compiled BinaryArgmin.installFirst 8 2

/-- The first incumbent is installed by finite copying instructions. -/
theorem install_trace_space (B C : ℕ) (next : BinaryArgmin.Entry)
    (frame : List Bool) (regs : Fin 8 → Bool)
    (hn : next.score.length = B) (hcn : next.payload.length ≤ C) :
    ∃ steps ≤ 100 * (B + C + 1) + 1, ∃ regs',
      Trace installProgram steps
        ((BinaryArgmin.data regs next BinaryArgmin.empty frame).withPC
          (some installProgram.entry))
        ((BinaryArgmin.data regs' BinaryArgmin.empty next frame).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace installProgram prefixSteps
          ((BinaryArgmin.data regs next BinaryArgmin.empty frame).withPC
            (some installProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          9 * (B + C + frame.length) + 100 * (B + C + 1) + 1 := by
  obtain ⟨steps, hsteps, regs', ht⟩ :=
    BinaryArgmin.installFirst_eval B C next frame regs ⟨hn, hcn⟩
  refine ⟨steps + 1, by omega, regs', compiled_halt_trace ht 8 2, ?_⟩
  intro prefixSteps intermediate hp htrace i
  have hinitial : dataBits
      ((BinaryArgmin.data regs next BinaryArgmin.empty frame).withPC
        (some installProgram.entry)) ≤ 9 * (B + C + frame.length) := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _j : Fin 9, (B + C + frame.length) := by
        apply Finset.sum_le_sum
        intro j _
        fin_cases j <;> simp [BinaryArgmin.data, BinaryArgmin.store, BinaryArgmin.empty] <;>
          omega
      _ = _ := by simp
  have hsize := trace_dataBits installProgram htrace
  have hport : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  omega

/-- The finite bit routine uses the same strict comparison as the cached
semantic update, retaining the incumbent on an equal score. -/
theorem update_numeric (best next : BinaryArgmin.Entry) :
    (BinaryArgmin.pick best next).payload =
      (HashGreedy.update (best.payload, BinaryArgmin.value best)
        next.payload (BinaryArgmin.value next)).1 ∧
    BinaryArgmin.value (BinaryArgmin.pick best next) =
      (HashGreedy.update (best.payload, BinaryArgmin.value best)
        next.payload (BinaryArgmin.value next)).2 := by
  unfold BinaryArgmin.pick HashGreedy.update
  split_ifs <;> exact ⟨rfl, rfl⟩


/-- Serialization uses the existing measured bit escaping routine. -/
def appendPorts : RecordPrograms.Ports 8 10 where
  tag := 0
  present := 1
  found := 7
  source := 2
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def appendWinner : Cmd 8 10 :=
  .seq (Subexp.TupleProgram.pushConst 9 0 false)
    (.seq (Subexp.TupleProgram.escape appendPorts)
      (.seq (Subexp.TupleProgram.pushConst 9 0 true)
        (.call (StackRoutines.clearProgram 3 0 1))))

def appended (a : State 8 10) : State 8 10 :=
  let b := Subexp.TupleProgram.pushedState 9 0 false a
  let c := Subexp.TupleProgram.escapedState appendPorts b
  let d := Subexp.TupleProgram.pushedState 9 0 true c
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 3 d.stacks⟩

/-- Exact measured appending, with no retained candidate family. -/
theorem append_eval (a : State 8 10) :
    Eval appendWinner (5 * (a.stacks 2).length + 2 * (a.stacks 3).length + 10)
      a (appended a) := by
  let b := Subexp.TupleProgram.pushedState 9 0 false a
  let c := Subexp.TupleProgram.escapedState appendPorts b
  let d := Subexp.TupleProgram.pushedState 9 0 true c
  have h1 := Subexp.TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) false a
  have h2 := Subexp.TupleProgram.escape_eval_state appendPorts b
  have h3 := Subexp.TupleProgram.pushConst_eval (9 : Fin 10) (0 : Fin 8) true c
  have h4 := Subexp.TupleProgram.clear_eval (3 : Fin 10) (0 : Fin 8) 1 d
  convert h1.seq (h2.seq (h3.seq h4)) using 1
  · rfl
  · simp [b, c, d, appendPorts]
    omega
  · rfl

theorem appended_history (a : State 8 10) :
    (appended a).stacks 9 =
      true :: (Encoding.frame (a.stacks 2).reverse ++ a.stacks 9) := by
  simp [appended, StackRoutines.clearStacks, appendPorts, Subexp.TupleProgram.frame_eq_escaped,
    List.append_assoc]

theorem appended_frame (a : State 8 10) (i : Fin 10)
    (h2 : i ≠ 2) (h3 : i ≠ 3) (h9 : i ≠ 9) :
    (appended a).stacks i = a.stacks i := by
  simp [appended, StackRoutines.clearStacks, appendPorts, h2, h3, h9]

/-- Exact retained history growth: one selected payload and its framing bits.
No trial payload or losing score is retained in the history stack. -/
theorem appended_history_length (a : State 8 10) :
    ((appended a).stacks 9).length =
      (a.stacks 9).length + 2 * (a.stacks 2).length + 2 := by
  rw [appended_history]
  simp only [List.length_cons, List.length_append, Encoding.length_frame, List.length_reverse]
  omega

/-- Only selected rows occur in this proof-level serialization. -/
def encodedHistory (rows : List (List Bool)) : List Bool :=
  Encoding.encodeList id (rows.map List.reverse)

theorem encodedHistory_length_le (rows : List (List Bool)) (C : ℕ)
    (hC : ∀ bits ∈ rows, bits.length ≤ C) :
    (encodedHistory rows).length ≤ rows.length * (2 * C + 2) + 1 := by
  induction rows with
  | nil => simp [encodedHistory, Encoding.encodeList]
  | cons bits rows ih =>
    have hb := hC bits (by simp)
    have hr := ih (fun word hw => hC word (by simp [hw]))
    simp only [encodedHistory, List.map_cons, Encoding.encodeList, id_eq,
      List.length_cons, List.length_append, Encoding.length_frame, List.length_reverse] at *
    nlinarith

@[simp] theorem appended_payload (a : State 8 10) : (appended a).stacks 2 = [] := by
  simp [appended, StackRoutines.clearStacks, appendPorts]

@[simp] theorem appended_score (a : State 8 10) : (appended a).stacks 3 = [] := by
  simp [appended, StackRoutines.clearStacks]

def appendProgram := compiled appendWinner 2 9

theorem append_trace_space (a : State 8 10) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    ∃ steps ≤ 7 * bound + 11,
      Trace appendProgram steps (a.withPC (some appendProgram.entry))
        ((appended a).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace appendProgram prefixSteps (a.withPC (some appendProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 17 * bound + 11 := by
  refine ⟨5 * (a.stacks 2).length + 2 * (a.stacks 3).length + 11,
    by have := ha 2; have := ha 3; omega,
    compiled_halt_trace (append_eval a) 2 9, ?_⟩
  intro prefixSteps intermediate hp ht i
  have hinitial : dataBits (a.withPC (some appendProgram.entry)) ≤ 10 * bound := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _i : Fin 10, bound := Finset.sum_le_sum fun i _ => ha i
      _ = _ := by simp
  have hgrowth := trace_dataBits appendProgram ht
  have hport : (intermediate.stacks i).length ≤ dataBits intermediate :=
    Finset.single_le_sum (fun j _ => Nat.zero_le ((intermediate.stacks j).length))
      (Finset.mem_univ i)
  have := ha 2
  have := ha 3
  omega


/-- Read the actual retained candidate and its full binary score. -/
def readEntry {r s : ℕ} (payload score : Fin s) (a : State r s) : BinaryArgmin.Entry :=
  ⟨a.stacks payload, a.stacks score⟩

theorem advance_readEntry {r s : ℕ} (p : CounterForPrograms.Ports r s)
    (payload score : Fin s) (a : State r s) (words : List (List Bool))
    (hpc : payload ≠ p.counter) (hps : payload ≠ p.scratch)
    (hsc : score ≠ p.counter) (hss : score ≠ p.scratch) :
    readEntry payload score (ExecCNFTupleEnumeration.advanceResult p a words) =
      readEntry payload score a := by
  apply congrArg₂ BinaryArgmin.Entry.mk
  · exact (ExecCNFTupleEnumeration.advanceResult_outside p a words payload hpc hps).symm
  · exact (ExecCNFTupleEnumeration.advanceResult_outside p a words score hsc hss).symm

/-- Refinement of a genuine iterator trace to the cached strict argmin.
`ranks` is proof evidence of visits, never a machine stack or runtime list.
The body premise concerns its actual measured execution and must be discharged
by candidate loading, normalization, exact scoring, and `updateProgram`. -/
theorem visits_best {r s : ℕ} (p : CounterForPrograms.Ports r s)
    (body : Cmd r s) (shape : List ℕ) (payload score : Fin s)
    (entry : ℕ → BinaryArgmin.Entry) (I : State r s → Prop)
    (hpc : payload ≠ p.counter) (hps : payload ≠ p.scratch)
    (hsc : score ≠ p.counter) (hss : score ≠ p.scratch)
    (hbody : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a b → I a →
      readEntry payload score b = BinaryArgmin.pick (readEntry payload score a)
        (entry (CounterPrograms.value words.flatten)) ∧
      I (ExecCNFTupleEnumeration.advanceResult p b words))
    {ranks : List ℕ} {steps : ℕ} {a b : State r s}
    (hvis : ExecCNFTupleEnumeration.Visits p body shape ranks steps a b) (hI : I a) :
    readEntry payload score b = HashSelect.best BinaryArgmin.value
      (readEntry payload score a) (ranks.map entry) := by
  induction hvis with
  | done a hf => rfl
  | @step words a middle b nb na nt ranks hf hw hc hb he ha tail ih =>
    obtain ⟨hselected, hnext⟩ := hbody words a middle nb hw hc hb hI
    rw [ih hnext, advance_readEntry p payload score middle words hpc hps hsc hss,
      hselected]
    rfl

/-- Every losing callback contributes a comparison constraint on the actual
returned binary score, not only on a semantic annotation. -/
theorem visits_minimum {r s : ℕ} (p : CounterForPrograms.Ports r s)
    (body : Cmd r s) (shape : List ℕ) (payload score : Fin s)
    (entry : ℕ → BinaryArgmin.Entry) (I : State r s → Prop)
    (hpc : payload ≠ p.counter) (hps : payload ≠ p.scratch)
    (hsc : score ≠ p.counter) (hss : score ≠ p.scratch)
    (hbody : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a b → I a →
      readEntry payload score b = BinaryArgmin.pick (readEntry payload score a)
        (entry (CounterPrograms.value words.flatten)) ∧
      I (ExecCNFTupleEnumeration.advanceResult p b words))
    {ranks : List ℕ} {steps : ℕ} {a b : State r s}
    (hvis : ExecCNFTupleEnumeration.Visits p body shape ranks steps a b) (hI : I a) :
    readEntry payload score b ∈ readEntry payload score a :: ranks.map entry ∧
      ∀ j ∈ ranks, BinaryArgmin.value (readEntry payload score b) ≤
        BinaryArgmin.value (entry j) := by
  rw [visits_best p body shape payload score entry I hpc hps hsc hss hbody hvis hI]
  refine ⟨HashSelect.best_mem _ _ _, ?_⟩
  intro j hj
  exact HashSelect.best_le_member _ _ _ _ (List.mem_map.mpr ⟨j, hj, rfl⟩)


/-- Complete coverage and measured time of the actual overflow-controlled
scan. The single seeded incumbent is paid separately by `install_trace_space`.
Callback correctness is an intermediate implementation contract. -/
theorem enumerate_minimum {r s : ℕ} (p : CounterForPrograms.Ports r s)
    (body : Cmd r s) (shape : List ℕ) (payload score : Fin s)
    (entry : ℕ → BinaryArgmin.Entry) (I : State r s → Prop) (budget : ℕ)
    (stable : CounterForPrograms.FrameStable p (fun _ => I))
    (spec : ExecCNFTupleEnumeration.BodySpec p body shape I budget)
    (hpc : payload ≠ p.counter) (hps : payload ≠ p.scratch)
    (hsc : score ≠ p.counter) (hss : score ≠ p.scratch)
    (hbody : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a b → I a →
      readEntry payload score b = BinaryArgmin.pick (readEntry payload score a)
        (entry (CounterPrograms.value words.flatten)) ∧
      I (ExecCNFTupleEnumeration.advanceResult p b words))
    (words : List (List Bool)) (a : State r s)
    (hshape : words.map List.length = shape) (hI : I a)
    (hc : a.stacks p.counter = Encoding.encodeList id words)
    (hs : a.stacks p.scratch = []) (hz : CounterPrograms.value words.flatten = 0)
    (hseed : readEntry payload score a = entry 0) :
    ∃ steps ≤ 2 ^ words.flatten.length *
        (budget + 7 * (Encoding.encodeList id words).length + 5) + 2,
      ∃ b, Eval (ExecCNFTupleEnumeration.enumerate p body) steps a b ∧ I b ∧
        (∃ j < 2 ^ words.flatten.length, readEntry payload score b = entry j) ∧
        (∀ j < 2 ^ words.flatten.length,
          BinaryArgmin.value (readEntry payload score b) ≤ BinaryArgmin.value (entry j)) ∧
        b.stacks p.counter = Encoding.encodeList id
          (shape.map (fun width => List.replicate width false)) := by
  obtain ⟨steps, b, he, hv, hb, _, _, hsteps⟩ :=
    ExecCNFTupleEnumeration.enumerate_correct p body shape I budget stable spec words a
      hshape hI hc hs hz
  have hstart : I (ExecCNFTupleEnumeration.startResult p a) :=
    stable 0 a _ (fun _ _ _ => rfl) hI
  obtain ⟨hmem, hmin⟩ := visits_minimum p body shape payload score entry I
    hpc hps hsc hss hbody hv hstart
  have hread : readEntry payload score (ExecCNFTupleEnumeration.startResult p a) =
      readEntry payload score a := rfl
  rw [hread, hseed] at hmem
  refine ⟨1 + steps, hsteps, b, he, hb, ?_, ?_, ?_⟩
  · rcases List.mem_cons.mp hmem with hfirst | hrest
    · exact ⟨0, by positivity, hfirst⟩
    · obtain ⟨j, hj, hentry⟩ := List.mem_map.mp hrest
      exact ⟨j, by simpa using hj, hentry.symm⟩
  · intro j hj
    exact hmin j (by simpa using hj)
  · exact Enumerators.visits_reset_counter hv (ExecCNFTupleEnumeration.startResult_flag p a)


namespace PadScore

open ModularPrograms ModularArithmetic

def data (regs : Fin 8 → Bool) (score shape : List Bool) : State 8 5 :=
  ⟨regs, ![score,shape,[],[],[]]⟩

def pads : Fin 3 → Fin 5 := ![2,0,3]

private theorem pads_injective : Function.Injective pads := by decide

/-- The fixed-width shape is copied before padding, and survives every score.
Only the actual canonical mass word is padded; the final exact count has its
own canonical output path. -/
def command : Cmd 8 5 :=
  .seq (.call (StackRoutines.copyProgram 1 2 4 0 1))
    (.seq (.call (ProgramLinking.liftProgram paddingLEProgram id pads))
      (.seq (.call (StackRoutines.copyProgram 2 0 4 0 1))
        (.call (StackRoutines.clearProgram 2 0 1))))

theorem command_eval (regs : Fin 8 → Bool) (score shape : List Bool)
    (hlen : score.length ≤ shape.length) :
    ∃ rf, Eval command (23 * shape.length + 19) (data regs score shape)
      (data rf (padTo shape score) shape) := by
  let a := data regs score shape
  let r1 := readRegs regs 0 1 none
  let a1 : State 8 5 := ⟨r1, ![score,shape,shape,[],[]]⟩
  have h1 := Subexp.TupleProgram.copy_eval (1 : Fin 5) 2 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a rfl
  have he1 : (⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 1 2 a.stacks⟩ :
      State 8 5) = a1 := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    funext i
    fin_cases i <;> simp [a, data, StackRoutines.copyStacks]
  rw [he1] at h1
  obtain ⟨r2, h2, _⟩ := paddingLE_correct r1 shape score hlen
  let d2 : State 8 3 := ⟨r2, operandStacks (padTo shape score) [] []⟩
  have h2' : Trace paddingLEProgram (7 * shape.length + 6)
      ((projectState id pads a1).withPC (some paddingLEProgram.entry)) (d2.withPC none) := by
    have hproject : projectState id pads a1 = ⟨r1, operandStacks shape score []⟩ := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext i; fin_cases i <;> rfl
    rw [hproject]
    have hentry : paddingLEProgram.entry = (0 : Fin 9) := by
      apply Fin.ext
      rfl
    rw [hentry]
    exact h2
  have he2 := eval_call_from_state paddingLEProgram id pads a1
    Function.injective_id pads_injective h2'
  let a2 : State 8 5 := ⟨r2, ![[],shape,padTo shape score,[],[]]⟩
  have ha2 : embedState id pads a1 d2 = a2 := by
    apply embedState_eq_of_ports id pads a1 a2 d2 Function.injective_id pads_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i
      · exact False.elim (hi ⟨1, rfl⟩)
      · rfl
      · exact False.elim (hi ⟨0, rfl⟩)
      · rfl
      · rfl
  rw [ha2] at he2
  have h3 := Subexp.TupleProgram.copy_eval (2 : Fin 5) 0 4 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a2 rfl
  let a3 : State 8 5 := ⟨readRegs r2 0 1 none,
    ![padTo shape score,shape,padTo shape score,[],[]]⟩
  have ha3 : (⟨readRegs a2.regs 0 1 none, StackRoutines.copyStacks 2 0 a2.stacks⟩ :
      State 8 5) = a3 := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    funext i
    fin_cases i <;> simp [a2, StackRoutines.copyStacks]
  rw [ha3] at h3
  have h4 := Subexp.TupleProgram.clear_eval (2 : Fin 5) (0 : Fin 8) 1 a3
  have ha4 : (⟨readRegs a3.regs 0 1 none, StackRoutines.clearStacks 2 a3.stacks⟩ :
      State 8 5) = data (readRegs r2 0 1 none) (padTo shape score) shape := by
    apply congrArg₂ StructuredProgram.State.mk
    · exact StackRoutines.readRegs_reset r2 0 1 none
    funext i
    fin_cases i <;> simp [a3, StackRoutines.clearStacks]
  rw [ha4] at h4
  refine ⟨readRegs r2 0 1 none, ?_⟩
  convert h1.seq (he2.seq (h3.seq h4)) using 1
  · rfl
  · simp [a, a2, a3, data, padTo_length]
    omega

theorem exact_value (score shape : List Bool) (hlen : score.length ≤ shape.length) :
    BinaryArithmetic.toNat (padTo shape score) = BinaryArithmetic.toNat score ∧
      (padTo shape score).length = shape.length :=
  ⟨padTo_correct shape score hlen, padTo_length shape score⟩

def program := compiled command 0 0

theorem trace_space (regs : Fin 8 → Bool) (score shape : List Bool)
    (hlen : score.length ≤ shape.length) :
    ∃ rf, Trace program (23 * shape.length + 20)
      ((data regs score shape).withPC (some program.entry))
      ((data rf (padTo shape score) shape).withPC none) ∧
      ∀ k c, k ≤ 23 * shape.length + 20 →
        Trace program k ((data regs score shape).withPC (some program.entry)) c →
        ∀ i, (c.stacks i).length ≤ 25 * shape.length + 20 := by
  obtain ⟨rf, he⟩ := command_eval regs score shape hlen
  refine ⟨rf, compiled_halt_trace he 0 0, ?_⟩
  have hb : dataBits ((data regs score shape).withPC (some program.entry)) ≤
      2 * shape.length := by
    simp [dataBits, stackBits, data, Fin.sum_univ_succ]
    omega
  intro k c hk hc i
  have h := StructuredSpace.local_stack_bound program (steps := 23 * shape.length + 20)
    hb k c hk hc i
  omega

/-- The query owns the low scratch bank; the retained selector score and
fixed unary shape are outside it. All other selector stacks are framed. -/
def leafRegisters : Fin 8 → Fin 40 := Fin.castAdd 32

def leafStacks : Fin 5 → Fin 896 := ![769,818,0,1,2]

def leafCommand : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram program leafRegisters leafStacks)

theorem leaf_eval (a : State 40 896) (h0 : a.stacks 0 = [])
    (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hlen : (a.stacks 769).length ≤ (a.stacks 818).length) :
    ∃ b, Eval leafCommand (23 * (a.stacks 818).length + 20) a b ∧
      b.stacks = Function.update a.stacks 769
        (padTo (a.stacks 818) (a.stacks 769)) := by
  let d := projectState leafRegisters leafStacks a
  have hd : d = data d.regs (a.stacks 769) (a.stacks 818) := by
    apply CounterForPrograms.data_ext (a := d)
      (b := data d.regs (a.stacks 769) (a.stacks 818)) rfl
    funext i
    fin_cases i <;> simp [d, data, projectState, leafStacks, h0, h1, h2]
  obtain ⟨rf, ht, _⟩ := trace_space d.regs (a.stacks 769) (a.stacks 818) hlen
  rw [← hd] at ht
  have hr : Function.Injective leafRegisters := Fin.castAdd_injective 8 32
  have hs : Function.Injective leafStacks := by decide
  let out := data rf (padTo (a.stacks 818) (a.stacks 769)) (a.stacks 818)
  refine ⟨embedState leafRegisters leafStacks a out,
    eval_call_from_state program leafRegisters leafStacks a hr hs ht, ?_⟩
  have hout : out.stacks = Function.update d.stacks 0
      (padTo (a.stacks 818) (a.stacks 769)) := by
    funext i
    fin_cases i <;> simp [out, data, d, projectState, leafStacks, h0, h1, h2]
  change Function.extend leafStacks out.stacks a.stacks = _
  rw [hout, ProgramLinking.extend_update hs]
  have hf : Function.extend leafStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project leafRegisters leafStacks a hr hs)
  rw [hf]
  rfl

end PadScore

namespace Initialize

open LeafOuterProgram

def savedRoutes : List Route := [(773,817),(768,780),(774,781)]

def registers : Fin 3 → Fin 40 := Fin.castAdd 37

def normalizeStacks : Fin 3 → Fin 896 := ![780,0,1]
def unaryStacks : Fin 3 → Fin 896 := ![781,0,1]

def normalize : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram CounterNormalizeProgram.program registers normalizeStacks)

def unary : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram registers unaryStacks)

def transfer : Cmd 40 896 := .call (StackRoutines.transferProgram 0 781 0 1)

/-- Three measured parameter copies, positive modulus normalization, and the
actual conversion from binary round count to the unary loop controller. -/
def command : Cmd 40 896 :=
  .seq (routes savedRoutes) (.seq normalize (.seq unary transfer))

private theorem register_injective : Function.Injective registers :=
  Fin.castAdd_injective 3 37

private theorem normalize_injective : Function.Injective normalizeStacks := by decide
private theorem unary_injective : Function.Injective unaryStacks := by decide

/-- A native positive normalizer changes only the modulus word. -/
theorem normalize_eval (a : Data) (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (hp : 0 < CounterPrograms.value (a.stacks 780)) :
    ∃ n ≤ 9 * (a.stacks 780).length + 21, ∃ b,
      Eval normalize n a b ∧
      b.stacks = Function.update a.stacks 780
        (CounterNormalizeProgram.normalized (a.stacks 780)) := by
  let d := projectState registers normalizeStacks a
  have hd : d = CounterNormalizeProgram.state d.regs (a.stacks 780) [] := by
    apply CounterForPrograms.data_ext (a := d) (b := CounterNormalizeProgram.state d.regs (a.stacks 780) []) rfl
    funext i
    fin_cases i <;> simp [d, projectState, normalizeStacks, CounterNormalizeProgram.state, h0, h1]
  obtain ⟨n, hn, ht⟩ := CounterNormalizeProgram.normalize_runs d.regs (a.stacks 780) hp
  rw [← hd, ← CounterNormalizeProgram.normalized_eq_fixedBits _ hp] at ht
  let out := CounterNormalizeProgram.state CounterNormalizeProgram.zeroRegs
    (CounterNormalizeProgram.normalized (a.stacks 780)) []
  refine ⟨n, hn, embedState registers normalizeStacks a out,
    eval_call_from_state _ _ _ a register_injective normalize_injective ht, ?_⟩
  have hs : out.stacks = Function.update d.stacks 0
      (CounterNormalizeProgram.normalized (a.stacks 780)) := by
    funext i
    fin_cases i <;> simp [out, d, projectState, normalizeStacks, CounterNormalizeProgram.state, h0, h1]
  change Function.extend normalizeStacks out.stacks a.stacks = _
  rw [hs, ProgramLinking.extend_update normalize_injective]
  have hf : Function.extend normalizeStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers normalizeStacks a register_injective normalize_injective)
  rw [hf]
  rfl

/-- The round counter is converted physically; its value, rather than its
binary word length, becomes the number of future rounds. -/
theorem unary_eval (a : Data) (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) :
    ∃ n ≤ CounterConversions.runtimeBound (a.stacks 781), ∃ b,
      Eval unary n a b ∧
      b.stacks = Function.update (Function.update a.stacks 781 []) 0
        (List.replicate (CounterPrograms.value (a.stacks 781)) true) := by
  let d := projectState registers unaryStacks a
  have hd : d = CounterConversions.state d.regs (a.stacks 781) [] := by
    apply CounterForPrograms.data_ext (a := d) (b := CounterConversions.state d.regs (a.stacks 781) []) rfl
    funext i
    fin_cases i <;> simp [d, projectState, unaryStacks, CounterConversions.state, h0, h1]
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs d.regs (a.stacks 781) []
  rw [← hd, List.append_nil] at ht
  let out := CounterConversions.state CounterConversions.zeroRegs []
    (List.replicate (CounterPrograms.value (a.stacks 781)) true)
  refine ⟨n, hn, embedState registers unaryStacks a out,
    eval_call_from_state _ _ _ a register_injective unary_injective ht, ?_⟩
  have hs : out.stacks = Function.update (Function.update d.stacks 0 []) 1
      (List.replicate (CounterPrograms.value (a.stacks 781)) true) := by
    funext i
    fin_cases i <;> simp [out, d, projectState, unaryStacks, CounterConversions.state, h1]
  change Function.extend unaryStacks out.stacks a.stacks = _
  rw [hs, ProgramLinking.extend_update unary_injective,
    ProgramLinking.extend_update unary_injective]
  have hf : Function.extend unaryStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers unaryStacks a register_injective unary_injective)
  rw [hf]
  rfl

def resultStacks (a : Data) : Fin 896 → List Bool :=
  Function.update (Function.update (Function.update a.stacks 817 (a.stacks 773))
    780 (CounterNormalizeProgram.normalized (a.stacks 768)))
    781 (List.replicate (CounterPrograms.value (a.stacks 774)) true)

/-- Actual initializer, including every copy, arithmetic microstep, unary
output bit, and return. The enclosing measured preparer supplies the initial
scratch invariant when this local routine is integrated. -/
theorem command_eval (a : Data) (L : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (ht : a.stacks 767 = [])
    (hp : 0 < CounterPrograms.value (a.stacks 768)) :
    ∃ n ≤ 100 * (CounterPrograms.value (a.stacks 774) + 1) * (L + 1), ∃ b,
      Eval command n a b ∧ b.stacks = resultStacks a := by
  have hv : ∀ p ∈ savedRoutes, routeValid p := by
    intro p hp
    simp only [savedRoutes, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> unfold routeValid <;> decide
  let a1 := routesState savedRoutes a
  have hcopy := routes_eval savedRoutes hv a ht
  have hcost := routes_cost_bound savedRoutes a L hL
  have hs : a1.stacks = Function.update (Function.update
      (Function.update a.stacks 817 (a.stacks 773)) 780 (a.stacks 768)) 781 (a.stacks 774) := by
    simp [a1, savedRoutes, routesState, routed]
  obtain ⟨u, hu, a2, he2, hs2⟩ := normalize_eval a1
    (by simp [hs, h0]) (by simp [hs, h1]) (by simpa [hs] using hp)
  obtain ⟨v, hv, a3, he3, hs3⟩ := unary_eval a2
    (by simp [hs2, hs, h0]) (by simp [hs2, hs, h1])
  have he4 := Subexp.TupleProgram.transfer_eval (0 : Fin 896) 781 (0 : Fin 40) 1
    (by decide) (by decide) a3
  let b : Data := ⟨readRegs a3.regs 0 1 none, StackRoutines.transferStacks 0 781 a3.stacks⟩
  refine ⟨routesCost savedRoutes a + (u + (v + (3 * (a3.stacks 0).length + 3))),
    ?_, b, hcopy.seq (he2.seq (he3.seq he4)), ?_⟩
  · have hw := hL 768
    have hr := hL 774
    change routesCost savedRoutes a ≤ 3 * (9 * L + 8) + 3 at hcost
    simp only [hs2, hs, Function.update_self, Function.update_of_ne (by decide : (781 : Fin 896) ≠ 780),
      CounterConversions.runtimeBound] at hv
    have hl : (a1.stacks 780).length = (a.stacks 768).length := by simp [hs]
    have hl0 : (a3.stacks 0).length = CounterPrograms.value (a.stacks 774) := by simp [hs3, hs2, hs]
    rw [hl] at hu
    rw [hl0]
    have hprod := Nat.mul_le_mul_left (32 * (CounterPrograms.value (a.stacks 774) + 1)) (Nat.add_le_add_right hr 1)
    nlinarith [Nat.zero_le (CounterPrograms.value (a.stacks 774) * L)]
  · funext i
    by_cases hi0 : i = 0
    · subst i
      simp [b, StackRoutines.transferStacks, resultStacks, h0]
    by_cases hi781 : i = 781
    · subst i
      simp [b, StackRoutines.transferStacks, hs3, hs2, hs, resultStacks]
    by_cases hi780 : i = 780 <;>
      simp [b, StackRoutines.transferStacks, hs3, hs2, hs, resultStacks, hi0, hi781, hi780,
        Function.update_apply]

/-- Saved modulus has the exact canonical width used in the fixed-square
candidate-count estimate, even if the arithmetic preparer emitted padding. -/
theorem result_modulus {m : ℕ} (a : Data) (hm : 0 < m)
    (hv : CounterPrograms.value (a.stacks 768) = 3 * m) :
    CounterPrograms.value (resultStacks a 780) = 3 * m ∧
      (resultStacks a 780).length = HashCandidates.digitWidth m := by
  have hp : 0 < CounterPrograms.value (a.stacks 768) := by omega
  simp [resultStacks, CounterNormalizeProgram.normalized_value _ hp,
    CounterNormalizeProgram.normalized_length, hv, HashCandidates.digitWidth,
    DyadicWidth.width, Nat.log2_eq_log_two]

def program := compiled command 768 781

/-- The initializer is polynomial work, so its complete local trace bounds
all stack prefixes, including its persistent saved parameters. -/
theorem trace_space (a : Data) (L : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (ht : a.stacks 767 = [])
    (hp : 0 < CounterPrograms.value (a.stacks 768)) :
    ∃ n ≤ 100 * (CounterPrograms.value (a.stacks 774) + 1) * (L + 1) + 1, ∃ b : Data,
      Trace program n (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks = resultStacks a ∧
      ∀ k c, k ≤ n → Trace program k (a.withPC (some program.entry)) c →
        ∀ i, (c.stacks i).length ≤
          896 * L + 100 * (CounterPrograms.value (a.stacks 774) + 1) * (L + 1) + 1 := by
  obtain ⟨n, hn, b, he, hb⟩ := command_eval a L hL h0 h1 ht hp
  refine ⟨n + 1, by omega, b, compiled_halt_trace he 768 781, hb, ?_⟩
  intro k c hk hc i
  have hinit : dataBits (a.withPC (some program.entry)) ≤ 896 * L := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _i : Fin 896, L := Finset.sum_le_sum fun i _ => hL i
      _ = _ := by simp
  have hbound := StructuredSpace.local_stack_bound program (steps := n + 1) hinit k c hk hc i
  omega


/-- Only the fixed nine-port argmin core is reset after its three prepared
parameters have been saved. History, formula, and count output are framed. -/
def corePorts : List (Fin 896) := [768,769,770,771,772,773,774,775,776]

def clearCore : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 corePorts

def coreCleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks corePorts a.stacks⟩

theorem clearCore_eval (a : Data) (L : ℕ)
    (hL : ∀ i ∈ corePorts, (a.stacks i).length ≤ L) (ht : a.stacks 767 = []) :
    ∃ n ≤ 18 * L + 30, Eval clearCore n a (coreCleared a) := by
  have h := BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 corePorts
    (by decide) a.regs a.stacks ht
  have sumBound (ps : List (Fin 896)) (hw : ∀ i ∈ ps, (a.stacks i).length ≤ L) :
      (ps.map (fun i => (a.stacks i).length)).sum ≤ ps.length * L := by
    induction ps with
    | nil => simp
    | cons i ps ih =>
      have hi := hw i (by simp)
      have hh := ih (fun j hj => hw j (by simp [hj]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  refine ⟨_, ?_, h⟩
  have hh := sumBound corePorts hL
  have hl : corePorts.length = 9 := rfl
  rw [hl] at hh ⊢
  omega

/-- Preserve the initial unary round count as a fixed score width before the
round controller starts consuming its own copy. This is separate from numeric
preparation because initial deterministic rows must be serialized at the same
canonical width before the argmin core is cleared. -/
def saveShape : Cmd 40 896 := route (781,818)

theorem saveShape_eval (a : Data) (ht : a.stacks 767 = []) :
    Eval saveShape (routeCost (781,818) a) a (routed (781,818) a) :=
  route_eval (781,818) (by unfold routeValid; decide) a ht

/-- Invoke only after the initial deterministic history is constructed using
the canonical width. This stage never repeats numerical preparation. -/
def finishSetup : Cmd 40 896 := .seq saveShape clearCore

def finishedStacks (a : Data) : Fin 896 → List Bool :=
  BankRoutines.clearBankStacks corePorts (Function.update a.stacks 818 (a.stacks 781))

theorem finishSetup_eval (a : Data) (L : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (ht : a.stacks 767 = []) :
    ∃ n ≤ 27 * L + 38, ∃ b,
      Eval finishSetup n a b ∧ b.stacks = finishedStacks a := by
  let c := routed (781,818) a
  have hc := saveShape_eval a ht
  have hwidth : ∀ i ∈ corePorts, (c.stacks i).length ≤ L := by
    intro i hi
    by_cases heq : i = 818
    · subst i
      simpa [c, routed] using hL 781
    · simpa [c, routed, heq] using hL i
  obtain ⟨q, hq, hclear⟩ := clearCore_eval c L hwidth (by simp [c, routed, ht])
  refine ⟨routeCost (781,818) a + q, ?_, coreCleared c, hc.seq hclear, rfl⟩
  have hsource := hL 781
  have htarget := hL 818
  change 2 * (a.stacks 818).length + 7 * (a.stacks 781).length + 8 + q ≤ 27 * L + 38
  omega

theorem finished_parameters (a : Data) :
    finishedStacks a 817 = a.stacks 817 ∧ finishedStacks a 780 = a.stacks 780 ∧
    finishedStacks a 781 = a.stacks 781 ∧ finishedStacks a 818 = a.stacks 781 ∧
    finishedStacks a 777 = a.stacks 777 ∧ finishedStacks a 784 = a.stacks 784 ∧
    finishedStacks a 788 = a.stacks 788 := by
  simp [finishedStacks, BankRoutines.clearBankStacks, corePorts]

def finishProgram := compiled finishSetup 781 818

theorem finish_trace_space (a : Data) (L : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (ht : a.stacks 767 = []) :
    ∃ n ≤ 27 * L + 39, ∃ b : Data,
      Trace finishProgram n (a.withPC (some finishProgram.entry)) (b.withPC none) ∧
      b.stacks = finishedStacks a ∧
      ∀ k c, k ≤ n → Trace finishProgram k (a.withPC (some finishProgram.entry)) c →
        ∀ i, (c.stacks i).length ≤ 923 * L + 39 := by
  obtain ⟨n, hn, b, he, hb⟩ := finishSetup_eval a L hL ht
  refine ⟨n + 1, by omega, b, compiled_halt_trace he 781 818, hb, ?_⟩
  intro k c hk hc i
  have hinit : dataBits (a.withPC (some finishProgram.entry)) ≤ 896 * L := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _i : Fin 896, L := Finset.sum_le_sum fun i _ => hL i
      _ = _ := by simp
  have hbound := StructuredSpace.local_stack_bound finishProgram (steps := n + 1) hinit k c hk hc i
  omega


/-- Physical construction of the one retained zero candidate. The depth
counter is copied from817; the canonical modulus780 determines chunk width. -/
def zeroStacks : Fin 6 → Fin 896 := ![1,778,0,780,2,3]

def zeroCommand : Cmd 40 896 :=
  .seq (.call (StackRoutines.clearProgram 778 0 1))
    (.seq (route (817,0))
      (.call (ProgramLinking.liftProgram HashCandidateProgram.ZeroCounter.program
        registers zeroStacks)))

def zeroWord (a : Data) : List Bool :=
  Encoding.encodeList id [List.replicate
    (CounterPrograms.value (a.stacks 817) * (a.stacks 780).length) false]

/-- No width product is materialized in binary or used as a host-language
loop: the finite constructor scans the modulus once for each binary depth
counter iteration, and charges every copied and emitted bit. -/
theorem zero_eval (a : Data) (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = []) (ht : a.stacks 767 = []) :
    ∃ n ≤ 100 * (CounterPrograms.value (a.stacks 817) + 1) *
        ((a.stacks 780).length + (a.stacks 817).length + (a.stacks 778).length + 1),
      ∃ b, Eval zeroCommand n a b ∧
        b.stacks = Function.update a.stacks 778 (zeroWord a) := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 778 a.stacks⟩
  have he1 := Subexp.TupleProgram.clear_eval (778 : Fin 896) (0 : Fin 40) 1 a
  let a2 := routed (817,0) a1
  have he2 := route_eval (817,0) (by unfold routeValid; decide) a1
    (by simp [a1, StackRoutines.clearStacks, ht])
  let d := projectState registers zeroStacks a2
  have hs : Function.Injective zeroStacks := by decide
  have hd : d = HashCandidateProgram.ZeroCounter.state d.regs [] []
      (a.stacks 817) (a.stacks 780) := by
    apply CounterForPrograms.data_ext (a := d)
      (b := HashCandidateProgram.ZeroCounter.state d.regs [] [] (a.stacks 817) (a.stacks 780)) rfl
    funext i
    fin_cases i <;> simp [d, projectState, zeroStacks, a2, routed, a1,
      StackRoutines.clearStacks, HashCandidateProgram.ZeroCounter.state, h1, h2, h3]
  obtain ⟨rf, q, hq, htrace⟩ := HashCandidateProgram.ZeroCounter.program_runs d.regs
    (a.stacks 817) (a.stacks 780)
  rw [← hd] at htrace
  let out := HashCandidateProgram.ZeroCounter.state rf [] (zeroWord a) [] (a.stacks 780)
  have he3 : Eval (.call (ProgramLinking.liftProgram HashCandidateProgram.ZeroCounter.program
      registers zeroStacks)) q a2 (embedState registers zeroStacks a2 out) :=
    eval_call_from_state _ _ _ a2 register_injective hs htrace
  refine ⟨2 * (a.stacks 778).length + 3 + (routeCost (817,0) a1 + q), ?_,
    embedState registers zeroStacks a2 out, he1.seq (he2.seq he3), ?_⟩
  · simp only [routeCost, a1, StackRoutines.clearStacks,
      Function.update_of_ne (by decide : (0 : Fin 896) ≠ 778),
      Function.update_of_ne (by decide : (817 : Fin 896) ≠ 778), h0, List.length_nil,
      Nat.mul_zero, Nat.zero_add]
    dsimp only [HashCandidateProgram.ZeroCounter.budget] at hq
    nlinarith [Nat.zero_le (CounterPrograms.value (a.stacks 817) * (a.stacks 778).length),
      Nat.zero_le (CounterPrograms.value (a.stacks 817) * (a.stacks 817).length),
      Nat.zero_le (CounterPrograms.value (a.stacks 817) * (a.stacks 780).length)]
  · have hout : out.stacks = Function.update (Function.update d.stacks 2 []) 1 (zeroWord a) := by
      funext i
      fin_cases i <;> simp [out, d, projectState, zeroStacks, a2, routed, a1,
        StackRoutines.clearStacks, HashCandidateProgram.ZeroCounter.state, h1, h2, h3]
    change Function.extend zeroStacks out.stacks a2.stacks = _
    rw [hout, ProgramLinking.extend_update hs, ProgramLinking.extend_update hs]
    have hf : Function.extend zeroStacks d.stacks a2.stacks = a2.stacks :=
      congrArg StructuredProgram.State.stacks
        (embedState_project registers zeroStacks a2 register_injective hs)
    rw [hf]
    funext i
    by_cases hi0 : i = 0
    · subst i
      simp [zeroStacks, a2, routed, a1, StackRoutines.clearStacks, h0]
    by_cases hi778 : i = 778
    · subst i
      simp [zeroStacks]
    simp [zeroStacks, a2, routed, a1, StackRoutines.clearStacks, hi0, hi778]

theorem zeroWord_length (a : Data) :
    (zeroWord a).length =
      2 * (CounterPrograms.value (a.stacks 817) * (a.stacks 780).length) + 3 := by
  simp [zeroWord, Encoding.encodeList, Encoding.length_frame]

theorem zeroWord_of_parameters (a : Data) (m depth : ℕ)
    (hdepth : CounterPrograms.value (a.stacks 817) = depth)
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m) :
    zeroWord a = Encoding.encodeList id
      [List.replicate (HashCandidates.payloadWidth m depth) false] := by
  simp only [zeroWord, hdepth, hwidth, HashCandidates.payloadWidth]

def zeroProgram := compiled zeroCommand 817 778

theorem zero_trace_space (a : Data) (L : ℕ) (hL : ∀ i, (a.stacks i).length ≤ L)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = [])
    (h2 : a.stacks 2 = []) (h3 : a.stacks 3 = []) (ht : a.stacks 767 = []) :
    ∃ n ≤ 100 * (CounterPrograms.value (a.stacks 817) + 1) * (3 * L + 1) + 1,
      ∃ b : Data, Trace zeroProgram n (a.withPC (some zeroProgram.entry)) (b.withPC none) ∧
        b.stacks = Function.update a.stacks 778 (zeroWord a) ∧
        ∀ k c, k ≤ n → Trace zeroProgram k (a.withPC (some zeroProgram.entry)) c →
          ∀ i, (c.stacks i).length ≤
            896 * L + 100 * (CounterPrograms.value (a.stacks 817) + 1) * (3 * L + 1) + 1 := by
  obtain ⟨n, hn, b, he, hb⟩ := zero_eval a h0 h1 h2 h3 ht
  have hbudget : n ≤ 100 * (CounterPrograms.value (a.stacks 817) + 1) * (3 * L + 1) := by
    apply hn.trans
    apply Nat.mul_le_mul_left
    have := hL 780
    have := hL 817
    have := hL 778
    omega
  refine ⟨n + 1, by omega, b, compiled_halt_trace he 817 778, hb, ?_⟩
  intro k c hk hc i
  have hinit : dataBits (a.withPC (some zeroProgram.entry)) ≤ 896 * L := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _i : Fin 896, L := Finset.sum_le_sum fun i _ => hL i
      _ = _ := by simp
  have hbound := StructuredSpace.local_stack_bound zeroProgram (steps := n + 1) hinit k c hk hc i
  omega

end Initialize

namespace NativeRound

/-- These are the fixed leaf ports, not an input-dependent bank allocation. -/
def registers : Fin 8 → Fin 40 := Fin.castAdd 32

def coreStacks : Fin 9 → Fin 896 := ![768,769,770,771,772,773,774,775,776]

def historyStacks : Fin 10 → Fin 896 := ![768,769,770,771,772,773,774,775,776,777]

def core : HashSelectProgram.Ports 40 896 where
  register := registers
  stack := coreStacks
  register_injective := Fin.castAdd_injective 8 32
  stack_injective := by decide

def counter : CounterForPrograms.Ports 40 896 where
  register := ⟨![0,1,9], by decide⟩
  counter := 778
  scratch := 779
  counter_ne_scratch := by decide

def outer : HashSelectProgram.LoopPorts 40 896 where
  value := 8
  present := 9
  counter := 781
  value_ne_present := by decide

/-- The four arithmetic scratch words and exhausted parser queue are empty at
candidate boundaries; retained best words are not part of this condition. -/
structure CoreClean (a : State 40 896) : Prop where
  scratch772 : a.stacks 772 = []
  scratch773 : a.stacks 773 = []
  scratch774 : a.stacks 774 = []
  scratch775 : a.stacks 775 = []
  queue776 : a.stacks 776 = []

private theorem projected_core (a : State 40 896) (hc : CoreClean a) :
    projectState registers coreStacks a = BinaryArgmin.data
      (fun i => a.regs (registers i)) (readEntry 768 769 a) (readEntry 770 771 a) [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  funext i
  fin_cases i <;> simp [coreStacks,
    BinaryArgmin.store, readEntry, hc.scratch772, hc.scratch773, hc.scratch774, hc.scratch775, hc.queue776]

def stored (a : State 40 896) (winner : BinaryArgmin.Entry) : Fin 896 → List Bool :=
  Function.update (Function.update (Function.update (Function.update a.stacks
    768 []) 769 []) 770 winner.payload) 771 winner.score

private theorem embed_core_stacks (a : State 40 896) (hc : CoreClean a)
    (rf : Fin 8 → Bool) (winner : BinaryArgmin.Entry) :
    (embedState registers coreStacks a (BinaryArgmin.data rf BinaryArgmin.empty winner [])).stacks =
      stored a winner := by
  let d := projectState registers coreStacks a
  have hout : (BinaryArgmin.data rf BinaryArgmin.empty winner []).stacks =
      Function.update (Function.update (Function.update (Function.update d.stacks
        0 []) 1 []) 2 winner.payload) 3 winner.score := by
    funext i
    fin_cases i <;> simp [d, projectState, coreStacks, BinaryArgmin.data,
      BinaryArgmin.store, BinaryArgmin.empty, hc.scratch772, hc.scratch773, hc.scratch774,
      hc.scratch775, hc.queue776]
  have hs : Function.Injective coreStacks := core.stack_injective
  change Function.extend coreStacks _ a.stacks = _
  rw [hout, ProgramLinking.extend_update hs,
    ProgramLinking.extend_update hs, ProgramLinking.extend_update hs,
    ProgramLinking.extend_update hs]
  have hf : Function.extend coreStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers coreStacks a
      core.register_injective core.stack_injective)
  rw [hf]
  rfl

/-- Actual score comparison, with an exact whole-bank frame statement. -/
theorem update_eval (a : State 40 896) (B C : ℕ) (hc : CoreClean a)
    (hn : BinaryArgmin.Fits B C (readEntry 768 769 a))
    (hb : BinaryArgmin.Fits B C (readEntry 770 771 a)) :
    ∃ n ≤ 100 * (B + C + 1) + 1, ∃ b,
      Eval (HashSelectProgram.update core) n a b ∧
      b.stacks = stored a (BinaryArgmin.pick (readEntry 770 771 a) (readEntry 768 769 a)) := by
  obtain ⟨n, hn', rf, he⟩ := BinaryArgmin.update_eval B C
    (readEntry 768 769 a) (readEntry 770 771 a) []
    (fun i => a.regs (registers i)) hn.1 hb.1 hn.2 hb.2
  have ht := compiled_halt_trace he 8 2
  rw [← projected_core a hc] at ht
  refine ⟨n + 1, by omega, _,
    eval_call_from_state _ registers coreStacks a
      core.register_injective core.stack_injective ht, ?_⟩
  exact embed_core_stacks a hc rf _

def install : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram HashGreedyProgram.installProgram registers coreStacks)

/-- Bootstrap pays the first full score and stores it by actual copying. -/
theorem install_eval (a : State 40 896) (B C : ℕ) (hc : CoreClean a)
    (hbp : a.stacks 770 = []) (hbs : a.stacks 771 = [])
    (hn : BinaryArgmin.Fits B C (readEntry 768 769 a)) :
    ∃ n ≤ 100 * (B + C + 1) + 1, ∃ b,
      Eval install n a b ∧
      b.stacks = stored a (readEntry 768 769 a) := by
  have hb : readEntry 770 771 a = BinaryArgmin.empty := by
    simp [readEntry, BinaryArgmin.empty, hbp, hbs]
  obtain ⟨n, hn', rf, he⟩ := BinaryArgmin.installFirst_eval B C
    (readEntry 768 769 a) [] (fun i => a.regs (registers i)) hn
  have ht := compiled_halt_trace he 8 2
  have hp := projected_core a hc
  rw [hb] at hp
  rw [← hp] at ht
  refine ⟨n + 1, by omega, _,
    eval_call_from_state _ registers coreStacks a
      core.register_injective core.stack_injective ht, ?_⟩
  exact embed_core_stacks a hc rf _

theorem stored_clean (a : State 40 896) (winner : BinaryArgmin.Entry)
    (hc : CoreClean a) (b : State 40 896) (hb : b.stacks = stored a winner) :
    CoreClean b ∧ b.stacks 768 = [] ∧ b.stacks 769 = [] ∧
      readEntry 770 771 b = winner := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [hb, stored, readEntry, hc.scratch772, hc.scratch773, hc.scratch774,
      hc.scratch775, hc.queue776]

/-- Every attempted candidate, including every loser, performs preparation,
exact mass evaluation, and physical fixed-width score padding. `mass` is fixed
finite syntax; its implementation proof remains an integration obligation. -/
def attempt (mass : Cmd 40 896) : Cmd 40 896 :=
  .seq HashCandidateProgram.Leaf.prepare (.seq mass PadScore.leafCommand)

/-- Physical padding connects an actual complete query trace to the selector
score ABI. This lemma assumes executions, never an unimplemented query oracle. -/
theorem attempt_eval_of_query (mass : Cmd 40 896) (a b c : State 40 896)
    (np nq : ℕ) (payload score : List Bool)
    (hp : Eval HashCandidateProgram.Leaf.prepare np a b)
    (hprep : b.stacks = Function.update a.stacks 768 payload)
    (hq : Eval mass nq b c)
    (hquery : c.stacks = Function.update b.stacks 769 score)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hlen : score.length ≤ (a.stacks 818).length) :
    ∃ d, Eval (attempt mass) (np + (nq + (23 * (a.stacks 818).length + 20))) a d ∧
      d.stacks = Function.update (Function.update a.stacks 768 payload) 769
        (ModularArithmetic.padTo (a.stacks 818) score) ∧
      BinaryArithmetic.toNat (d.stacks 769) = BinaryArithmetic.toNat score ∧
      (d.stacks 769).length = (a.stacks 818).length := by
  obtain ⟨d, he, hd⟩ := PadScore.leaf_eval c
    (by simp [hquery, hprep, h0]) (by simp [hquery, hprep, h1])
    (by simp [hquery, hprep, h2]) (by simpa [hquery, hprep] using hlen)
  have hf : d.stacks = Function.update (Function.update a.stacks 768 payload) 769
      (ModularArithmetic.padTo (a.stacks 818) score) := by
    simpa [hquery, hprep] using hd
  refine ⟨d, ?_, hf, ?_, ?_⟩
  · simpa only [attempt, hquery, hprep, Function.update_of_ne (by decide : (818 : Fin 896) ≠ 769),
      Function.update_of_ne (by decide : (818 : Fin 896) ≠ 768)] using hp.seq (hq.seq he)
  · simpa [hf] using (PadScore.exact_value score (a.stacks 818) hlen).1
  · simp [hf, ModularArithmetic.padTo_length]

def body (mass : Cmd 40 896) : Cmd 40 896 :=
  .seq (attempt mass) (HashSelectProgram.update core)

/-- Once the actual preparation/query/padding trace is supplied, the cached
minimum step follows with every other stack preserved. -/
theorem body_eval_of_attempt (mass : Cmd 40 896) (a b : State 40 896)
    (na B C : ℕ) (next : BinaryArgmin.Entry)
    (ha : Eval (attempt mass) na a b)
    (hframe : b.stacks = Function.update (Function.update a.stacks 768 next.payload) 769 next.score)
    (hc : CoreClean a) (hn : BinaryArgmin.Fits B C next)
    (hb : BinaryArgmin.Fits B C (readEntry 770 771 a)) :
    ∃ n ≤ na + (100 * (B + C + 1) + 1), ∃ c,
      Eval (body mass) n a c ∧
      c.stacks = stored a (BinaryArgmin.pick (readEntry 770 771 a) next) := by
  have hc' : CoreClean b := by
    constructor <;> simp [hframe, hc.scratch772, hc.scratch773, hc.scratch774,
      hc.scratch775, hc.queue776]
  have hn' : readEntry 768 769 b = next := by simp [readEntry, hframe]
  have hb' : readEntry 770 771 b = readEntry 770 771 a := by simp [readEntry, hframe]
  obtain ⟨n, hcost, c, he, hout⟩ := update_eval b B C hc'
    (by simpa only [hn'] using hn) (by simpa only [hb'] using hb)
  refine ⟨na + n, by omega, c, ha.seq he, ?_⟩
  rw [hout, hn', hb']
  funext i
  by_cases h0 : i = 768 <;> by_cases h1 : i = 769 <;>
    simp [stored, hframe, Function.update_apply, h0, h1]

def append : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram appendProgram registers historyStacks)

def appendedStacks (a : State 40 896) : Fin 896 → List Bool :=
  Function.update (Function.update (Function.update a.stacks 770 []) 771 []) 777
    (true :: (Encoding.frame (a.stacks 770).reverse ++ a.stacks 777))

/-- Serialize precisely one attained winner and clear its cached score. -/
theorem append_eval (a : State 40 896) :
    ∃ b, Eval append (5 * (a.stacks 770).length + 2 * (a.stacks 771).length + 11) a b ∧
      b.stacks = appendedStacks a := by
  let d := projectState registers historyStacks a
  have hr : Function.Injective registers := Fin.castAdd_injective 8 32
  have hs : Function.Injective historyStacks := by decide
  have he := HashGreedyProgram.append_eval d
  have ht := compiled_halt_trace he 2 9
  refine ⟨embedState registers historyStacks a (appended d),
    eval_call_from_state appendProgram registers historyStacks a hr hs ht, ?_⟩
  have hout : (appended d).stacks =
      Function.update (Function.update (Function.update d.stacks 2 []) 3 []) 9
        (true :: (Encoding.frame (d.stacks 2).reverse ++ d.stacks 9)) := by
    funext i
    by_cases h2 : i = 2
    · subst i
      simp
    by_cases h3 : i = 3
    · subst i
      simp
    by_cases h9 : i = 9
    · subst i
      simp [appended_history]
    simp only [Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h9, appended_frame d i h2 h3 h9]
  change Function.extend historyStacks _ a.stacks = _
  rw [hout, ProgramLinking.extend_update hs, ProgramLinking.extend_update hs,
    ProgramLinking.extend_update hs]
  have hf : Function.extend historyStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers historyStacks a hr hs)
  rw [hf]
  rfl

/-- The outer unary controller reads a preserved counter stack. Resetting its
flag after the inner scan is an actual charged instruction. -/
def resetGuard : Cmd 40 896 := .base (.atom (.set 9 true))

def guardSet (a : State 40 896) : State 40 896 :=
  ⟨Function.update a.regs 9 true, a.stacks⟩

theorem resetGuard_eval (a : State 40 896) : Eval resetGuard 1 a (guardSet a) :=
  .base (.atom _ _)

/-- One seed evaluation is paid before the full overflow-controlled scan.
The scan also visits zero; strict comparison makes the repeated seed harmless.
No exponential candidate list is present in the instruction sequence. -/
def round (mass : Cmd 40 896) : Cmd 40 896 :=
  .seq (attempt mass) (.seq install
    (.seq (ExecCNFTupleEnumeration.enumerate counter (body mass))
      (.seq append resetGuard)))

/-- Measured composition uses the actual execution of each fixed stage.
This is deliberately an intermediate trace lemma, not a closed query service. -/
theorem round_eval_of_stages (mass : Cmd 40 896)
    (a b c d e : State 40 896) (na ni ns np : ℕ)
    (ha : Eval (attempt mass) na a b)
    (hi : Eval install ni b c)
    (hs : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c d)
    (hp : Eval append np d e) :
    Eval (round mass) (na + (ni + (ns + (np + 1)))) a (guardSet e) :=
  ha.seq (hi.seq (hs.seq (hp.seq (resetGuard_eval e))))

/-- Every primitive source-table prefix of a stage, including every stack.
The bound is uniform across calls; it contains no completed-visit counter. -/
structure StageSpace (command : Cmd 40 896) (steps : ℕ)
    (a : State 40 896) (bound : ℕ) : Prop where
  bound : ∀ k c, k ≤ steps →
    Trace (compiled command 778 777) k
      (a.withPC (some (compiled command 778 777).entry)) c →
    ∀ i, (c.stacks i).length ≤ bound

theorem StageSpace.seq {first second : Cmd 40 896} {n m bound : ℕ}
    {a b c : State 40 896} (hf : Eval first n a b) (hs : Eval second m b c)
    (hfirst : StageSpace first n a bound) (hsecond : StageSpace second m b bound) :
    StageSpace (.seq first second) (n + m) a bound := by
  exact ⟨StructuredSpace.sequence_stack_bound hf hs 778 777 hfirst.bound hsecond.bound
    _ _ _ (compiled_site _ 778 777)⟩

theorem resetGuard_space (a : State 40 896) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound) : StageSpace resetGuard 1 a bound := by
  constructor
  intro k c hk ht i
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · cases ht
    exact hb i
  · rw [trace_same_length_unique ht (compiled_trace (resetGuard_eval a) 778 777)]
    exact hb i

/-- Stage bounds combine by their common maximum. In particular the number
of streamed candidates never multiplies the retained-space bound. -/
theorem round_space_of_stages (mass : Cmd 40 896)
    (a b c d e : State 40 896) (na ni ns np bound : ℕ)
    (ha : Eval (attempt mass) na a b) (hi : Eval install ni b c)
    (hs : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c d)
    (hp : Eval append np d e)
    (sa : StageSpace (attempt mass) na a bound) (si : StageSpace install ni b bound)
    (ss : StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c bound)
    (sp : StageSpace append np d bound) :
    StageSpace (round mass) (na + (ni + (ns + (np + 1)))) a bound := by
  have he : ∀ i, (e.stacks i).length ≤ bound :=
    sp.bound np _ le_rfl (compiled_trace hp 778 777)
  exact StageSpace.seq ha (hi.seq (hs.seq (hp.seq (resetGuard_eval e)))) sa
    (StageSpace.seq hi (hs.seq (hp.seq (resetGuard_eval e))) si
      (StageSpace.seq hs (hp.seq (resetGuard_eval e)) ss
        (StageSpace.seq hp (resetGuard_eval e) sp (resetGuard_space e bound he))))

/-- The actual final halt also obeys the same uniform source-prefix bound. -/
theorem round_halt_space_of_stages (mass : Cmd 40 896)
    (a b c d e : State 40 896) (na ni ns np bound : ℕ)
    (ha : Eval (attempt mass) na a b) (hi : Eval install ni b c)
    (hs : Eval (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c d)
    (hp : Eval append np d e)
    (sa : StageSpace (attempt mass) na a bound) (si : StageSpace install ni b bound)
    (ss : StageSpace (ExecCNFTupleEnumeration.enumerate counter (body mass)) ns c bound)
    (sp : StageSpace append np d bound) :
    StageSpace (round mass) (na + (ni + (ns + (np + 1))) + 1) a bound := by
  have he := round_eval_of_stages mass a b c d e na ni ns np ha hi hs hp
  have hb := round_space_of_stages mass a b c d e na ni ns np bound ha hi hs hp sa si ss sp
  exact ⟨StructuredSpace.compiled_halt_stack_bound he 778 777 hb.bound⟩

def rounds (mass : Cmd 40 896) : Cmd 40 896 := HashSelectProgram.rounds outer (round mass)

theorem readCounter_space (a : State 40 896) (bound : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ bound) :
    StageSpace (HashSelectProgram.readCounter outer) 1 a bound := by
  constructor
  intro k c hk ht i
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · cases ht
    exact hb i
  · rw [trace_same_length_unique ht
      (compiled_trace (HashSelectProgram.readCounter_eval outer a) 778 777)]
    by_cases hi : i = 781
    · subst i
      have := hb 781
      simp only [HashSelectProgram.readCounterState,
        outer, Function.update_self, List.length_tail]
      omega
    · simpa [StructuredProgram.State.withPC, HashSelectProgram.readCounterState,
        outer, hi] using hb i

/-- The outer unary loop also uses a uniform space invariant. Its round count
changes the time bound, never the maximum retained space. -/
theorem rounds_space (mass : Cmd 40 896) (I : State 40 896 → Prop) (bound : ℕ)
    (hbound : ∀ a, I a → ∀ i, (a.stacks i).length ≤ bound)
    (hread : ∀ a, I a → I (HashSelectProgram.readCounterState outer a))
    (hround : ∀ n a b, Eval (round mass) n a b → I a → a.regs 9 = true → I b)
    (hspace : ∀ n a b, Eval (round mass) n a b → I a → a.regs 9 = true →
      StageSpace (round mass) n a bound)
    {steps : ℕ} {a b : State 40 896} (he : Eval (rounds mass) steps a b) (hI : I a) :
    StageSpace (rounds mass) steps a bound := by
  let iteration := Cmd.seq (round mass) (HashSelectProgram.readCounter outer)
  have hpreserve : ∀ n x y, Eval iteration n x y → I x → x.regs 9 = true → I y := by
    intro n x y hx hIx hflag
    dsimp only [iteration] at hx
    cases hx with
    | @seq first second nr nd x middle y hr hd =>
      have hmiddle := hround nr x middle hr hIx hflag
      rw [hd.final_unique 778 (HashSelectProgram.readCounter_eval outer middle)]
      exact hread middle hmiddle
  have hbody : ∀ n x y, Eval iteration n x y → I x → x.regs 9 = true →
      StageSpace iteration n x bound := by
    intro n x y hx hIx hflag
    dsimp only [iteration] at hx
    cases hx with
    | @seq first second nr nd x middle y hr hd =>
      have hmiddle := hround nr x middle hr hIx hflag
      have hn := StreamResources.eval_steps_eq 778 777 hd
        (HashSelectProgram.readCounter_eval outer middle)
      subst nd
      exact StageSpace.seq hr hd (hspace nr x middle hr hIx hflag)
        (readCounter_space middle bound (hbound middle hmiddle))
  cases he with
  | @seq first second nr nl a middle b hr hl =>
    have hn := StreamResources.eval_steps_eq 778 777 hr
      (HashSelectProgram.readCounter_eval outer a)
    subst nr
    have hmiddle : I middle := by
      rw [hr.final_unique 778 (HashSelectProgram.readCounter_eval outer a)]
      exact hread a hI
    have hloop := StructuredSpace.loop_stack_bound iteration 9 778 777 I bound
      hbound hpreserve (fun n x y hx hIx hflag => (hbody n x y hx hIx hflag).bound)
      hl hmiddle
    exact StageSpace.seq hr hl (readCounter_space a bound (hbound a hI)) ⟨hloop⟩

def program (mass : Cmd 40 896) := compiled (rounds mass) 778 777

/-- A fixed explicit budget pays the seed, every visit and advance, the
retained winner append, and the outer flag reset. -/
def roundBudget (attemptCost scoreWidth payloadWidth : ℕ) : ℕ :=
  attemptCost + (100 * (scoreWidth + payloadWidth + 1) + 1) +
    (2 ^ payloadWidth * (attemptCost + 100 * (scoreWidth + payloadWidth + 1) + 1 +
      7 * (2 * payloadWidth + 3) + 5) + 2) +
    (5 * payloadWidth + 2 * scoreWidth + 11) + 1

theorem round_cost_le (attemptCost scoreWidth payloadWidth na ni ns np : ℕ)
    (ha : na ≤ attemptCost)
    (hi : ni ≤ 100 * (scoreWidth + payloadWidth + 1) + 1)
    (hs : ns ≤ 2 ^ payloadWidth *
      (attemptCost + 100 * (scoreWidth + payloadWidth + 1) + 1 +
        7 * (2 * payloadWidth + 3) + 5) + 2)
    (hp : np ≤ 5 * payloadWidth + 2 * scoreWidth + 11) :
    na + (ni + (ns + (np + 1))) ≤ roundBudget attemptCost scoreWidth payloadWidth := by
  unfold roundBudget
  omega

theorem round_budget_le (attemptCost scoreWidth payloadWidth : ℕ) :
    roundBudget attemptCost scoreWidth payloadWidth ≤
      400 * (2 ^ payloadWidth) * (attemptCost + scoreWidth + payloadWidth + 1) := by
  have hpositive : 1 ≤ 2 ^ payloadWidth := by
    have hp : 0 < (2 : ℕ) ^ payloadWidth := pow_pos (by decide) _
    omega
  unfold roundBudget
  nlinarith [Nat.mul_le_mul_left attemptCost hpositive,
    Nat.mul_le_mul_left scoreWidth hpositive,
    Nat.mul_le_mul_left payloadWidth hpositive]

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
