import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators

open BitProgram StructuredCalls ExecCNFTupleEnumeration

/-- The complete current tuple, including record delimiters, stays polynomial.
This is a bound on one word of data, not on the number of enumerated tuples. -/
theorem encoded_shape_length {words : List (List Bool)} {shape : List ℕ}
    (hshape : words.map List.length = shape) :
    (Encoding.encodeList id words).length = 2 * shape.sum + 2 * shape.length + 1 := by
  have hn := congrArg List.length hshape
  have hb := congrArg List.sum hshape
  simp only [List.length_map] at hn
  rw [ExecCNFTupleOdometer.encoded_length, hn]
  simpa only [List.length_flatten] using congrArg (fun n => 2 * n + 2 * shape.length + 1) hb

/-- A local increment has polynomial workspace independently of how many
other increments have preceded it. Every caller stack is included. -/
theorem advance_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (words : List (List Bool)) (d : StructuredCalls.State R S)
    (hc : d.stacks p.counter = Encoding.encodeList id words)
    (hs : d.stacks p.scratch = []) (boundaryBound : ℕ)
    (hb : ∀ i, (d.stacks i).length ≤ boundaryBound) :
    ∃ n, n ≤ 7 * (Encoding.encodeList id words).length + 4 ∧
      Eval (advanceCmd p) n d (advanceResult p d words) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace (compiled (advanceCmd p) p.counter p.counter) prefixSteps
          (d.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          S * boundaryBound + 7 * (Encoding.encodeList id words).length + 4 := by
  obtain ⟨n, hn, he⟩ := advance_eval p words d hc hs
  refine ⟨n, hn, he, ?_⟩
  intro prefixSteps intermediate hle htrace i
  have hb' : dataBits
      (d.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry)) ≤
      S * boundaryBound := StreamResources.dataBits_le_mul _ hb
  have hp := StructuredSpace.local_stack_bound
    (compiled (advanceCmd p) p.counter p.counter)
    (steps := 7 * (Encoding.encodeList id words).length + 4)
    hb' prefixSteps intermediate (hle.trans hn) htrace i
  simpa only [Nat.add_assoc] using hp

/-- Every actual callback and controller prefix has one common storage bound.
The number of visits does not appear in the bound. -/
theorem visits_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) (shape : List ℕ)
    (I J : StructuredCalls.State R S → Prop) (boundaryBound callbackBound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hmiddle : ∀ a, J a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hcallback : ∀ words a b nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a b → I a →
      a.regs (p.register 2) = true → J b ∧ b.stacks p.scratch = [] ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled body p.counter p.counter) prefixSteps
          (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    (hnext : ∀ words a, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → J a →
      I (advanceResult p a words))
    {ranks : List ℕ} {steps : ℕ} {a b : StructuredCalls.State R S}
    (hvis : Visits p body shape ranks steps a b) (hI : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (loopCmd p body) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (loopCmd p body) p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        max callbackBound (S * boundaryBound + 7 * (2 * shape.sum + 2 * shape.length + 1) + 4) := by
  let bound := max callbackBound
    (S * boundaryBound + 7 * (2 * shape.sum + 2 * shape.length + 1) + 4)
  have hboundary : boundaryBound ≤ bound := by
    have hS : 1 ≤ S := by have := p.counter.isLt; omega
    have hmul : boundaryBound ≤ S * boundaryBound := by
      simpa using Nat.mul_le_mul_right boundaryBound hS
    exact hmul.trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_max_right _ _)))
  induction hvis with
  | done a hf =>
      exact StructuredSpace.while_false_stack_bound _ _ a hf
        (fun i => (hinitial a hI i).trans hboundary)
        _ _ _ (compiled_site _ p.counter p.counter)
  | @step words a middle b nb na nt ranks hf hw hc hb he ha tail ih =>
      obtain ⟨hmid, hscratch, hbody⟩ := hcallback words a middle nb hw hc hb hI hf
      have hafter := hnext words middle hw he hmid
      obtain ⟨n, _, hn, hlocal⟩ := advance_stack_bound p words middle he hscratch
        boundaryBound (hmiddle middle hmid)
      have htime : na = n := StreamResources.eval_steps_eq p.counter p.counter ha hn
      have hcontrol : ∀ prefixSteps intermediate, prefixSteps ≤ na →
          Trace (compiled (advanceCmd p) p.counter p.counter) prefixSteps
            (middle.withPC (some (compiled (advanceCmd p) p.counter p.counter).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        rw [htime] at hle
        have h := hlocal prefixSteps intermediate hle htrace i
        rw [encoded_shape_length hw] at h
        exact h.trans (Nat.le_max_right _ _)
      have hcallbackBound : ∀ prefixSteps intermediate, prefixSteps ≤ nb →
          Trace (compiled body p.counter p.counter) prefixSteps
            (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        exact (hbody prefixSteps intermediate hle htrace i).trans (Nat.le_max_left _ _)
      have hsequence := StructuredSpace.sequence_stack_bound hb ha p.counter p.counter
        hcallbackBound hcontrol
        (compiled (.seq body (advanceCmd p)) p.counter p.counter)
        (siteAddress (.seq body (advanceCmd p))) (exitAddress (.seq body (advanceCmd p)))
        (compiled_site _ p.counter p.counter)
      exact StructuredSpace.while_true_stack_bound hf (.seq hb ha) tail.eval
        p.counter p.counter hsequence (ih hafter)
        _ _ _ (compiled_site _ p.counter p.counter)

/-- The iterator initialization and final halt preserve the loop's common
bound, so the theorem covers every prefix of the complete compiled program. -/
theorem enumerate_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) {shape ranks : List ℕ} {steps bound : ℕ}
    {a b : StructuredCalls.State R S}
    (hvis : Visits p body shape ranks steps (startResult p a) b)
    (hloop : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (loopCmd p body) p.counter p.counter) prefixSteps
        ((startResult p a).withPC
          (some (compiled (loopCmd p body) p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ 1 + steps + 1 →
      Trace (program p body) prefixSteps
        (a.withPC (some (program p body).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  have hstart : Eval (startCmd p) 1 a (startResult p a) := .base (.atom _ _)
  have hinit : ∀ i, (a.stacks i).length ≤ bound :=
    hloop 0 _ (Nat.zero_le _) (.refl _)
  have hprefix : ∀ prefixSteps intermediate, prefixSteps ≤ 1 →
      Trace (compiled (startCmd p) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (startCmd p) p.counter p.counter).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have ht : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
    rcases ht with rfl | rfl
    · cases htrace
      exact hinit i
    · have heq := trace_same_length_unique htrace (compiled_trace hstart p.counter p.counter)
      rw [heq]
      exact hinit i
  have hseq := StructuredSpace.sequence_stack_bound hstart hvis.eval p.counter p.counter
    hprefix hloop (program p body) (siteAddress (enumerate p body))
    (exitAddress (enumerate p body)) (compiled_site _ p.counter p.counter)
  exact StructuredSpace.compiled_halt_stack_bound (.seq hstart hvis.eval)
    p.counter p.counter hseq

/-- The binary countdown controller also retains a uniform stack bound for
arbitrarily many callbacks. Counter width is measured, never its numeric value. -/
theorem countdown_visits_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) (I J : StructuredCalls.State R S → Prop)
    (boundaryBound callbackBound : ℕ)
    (hinitial : ∀ a, I a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hmiddle : ∀ a, J a → ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hcallback : ∀ a b nb, Eval body nb a b → I a →
      a.regs (p.register 2) = true → 0 < CounterPrograms.value (a.stacks p.counter) →
      J b ∧ ∀ prefixSteps intermediate, prefixSteps ≤ nb →
        Trace (compiled body p.counter p.counter) prefixSteps
          (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ callbackBound)
    (hnext : ∀ a, J a → 0 < CounterPrograms.value (a.stacks p.counter) →
      I (CounterForPrograms.nextState p a))
    {costs : List ℕ} {steps : ℕ} {a b : StructuredCalls.State R S}
    (hvis : CounterForPrograms.Visits p body costs steps a b) (hI : I a) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter) prefixSteps
        (a.withPC
          (some (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤
          max callbackBound (S * boundaryBound + 16 * boundaryBound + 16) := by
  let bound := max callbackBound (S * boundaryBound + 16 * boundaryBound + 16)
  have hboundary : boundaryBound ≤ bound := by
    have hS : 1 ≤ S := by have := p.counter.isLt; omega
    have hmul : boundaryBound ≤ S * boundaryBound := by
      simpa using Nat.mul_le_mul_right boundaryBound hS
    exact hmul.trans ((Nat.le_add_right _ _).trans
      ((Nat.le_add_right _ _).trans (Nat.le_max_right _ _)))
  induction hvis with
  | done a hf hz =>
      exact StructuredSpace.while_false_stack_bound _ _ a hf
        (fun i => (hinitial a hI i).trans hboundary)
        _ _ _ (compiled_site _ p.counter p.counter)
  | @step a middle b nb nt costs hf hp hb hc hs tail ih =>
      obtain ⟨hmid, hbody⟩ := hcallback a middle nb hb hI hf hp
      have hpositive : 0 < CounterPrograms.value (middle.stacks p.counter) := by
        simpa only [hc] using hp
      have hafter := hnext middle hmid hpositive
      have ha := CounterForPrograms.advance_eval p middle hs
      have hcost := CounterForPrograms.advanceCost_le p middle hpositive
      have hwidth := hmiddle middle hmid p.counter
      have hcontrol : ∀ prefixSteps intermediate,
          prefixSteps ≤ CounterForPrograms.advanceCost p middle →
          Trace (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter) prefixSteps
            (middle.withPC
              (some (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter).entry))
            intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        have hb' : dataBits (middle.withPC
            (some (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter).entry)) ≤
            S * boundaryBound := StreamResources.dataBits_le_mul _ (hmiddle middle hmid)
        have h := StructuredSpace.local_stack_bound
          (compiled (CounterForPrograms.advanceCmd p) p.counter p.counter)
          (steps := 16 * boundaryBound + 16) hb' prefixSteps intermediate
          (by omega) htrace i
        exact h.trans (by
          simpa only [bound, Nat.add_assoc] using
            (Nat.le_max_right callbackBound (S * boundaryBound + 16 * boundaryBound + 16)))
      have hcallbackBound : ∀ prefixSteps intermediate, prefixSteps ≤ nb →
          Trace (compiled body p.counter p.counter) prefixSteps
            (a.withPC (some (compiled body p.counter p.counter).entry)) intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace i
        exact (hbody prefixSteps intermediate hle htrace i).trans (Nat.le_max_left _ _)
      have hsequence := StructuredSpace.sequence_stack_bound hb ha p.counter p.counter
        hcallbackBound hcontrol
        (compiled (.seq body (CounterForPrograms.advanceCmd p)) p.counter p.counter)
        (siteAddress (.seq body (CounterForPrograms.advanceCmd p)))
        (exitAddress (.seq body (CounterForPrograms.advanceCmd p)))
        (compiled_site _ p.counter p.counter)
      exact StructuredSpace.while_true_stack_bound hf (.seq hb ha) tail.eval
        p.counter p.counter hsequence (ih hafter)
        _ _ _ (compiled_site _ p.counter p.counter)

/-- The initial zero test and final halt are included in the counted loop's
prefix bound. The test scans only the current bounded-length counter word. -/
theorem countdown_for_stack_bound {R S : ℕ} (p : CounterForPrograms.Ports R S)
    (body : StructuredCalls.Cmd R S) {costs : List ℕ} {steps loopBound boundaryBound : ℕ}
    {a b : StructuredCalls.State R S} (hs : a.stacks p.scratch = [])
    (hinitial : ∀ i, (a.stacks i).length ≤ boundaryBound)
    (hvis : CounterForPrograms.Visits p body costs steps (CounterForPrograms.testResult p a) b)
    (hloop : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter) prefixSteps
        ((CounterForPrograms.testResult p a).withPC
          (some (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ loopBound) :
    ∀ prefixSteps intermediate,
      prefixSteps ≤ 8 * (a.stacks p.counter).length + 7 + steps + 1 →
      Trace (CounterForPrograms.program p body p.counter p.counter) prefixSteps
        (a.withPC (some (CounterForPrograms.program p body p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤
          max loopBound (S * boundaryBound + 8 * boundaryBound + 7) := by
  let bound := max loopBound (S * boundaryBound + 8 * boundaryBound + 7)
  have htest := CounterForPrograms.test_eval p a hs
  have hprefix : ∀ prefixSteps intermediate,
      prefixSteps ≤ 8 * (a.stacks p.counter).length + 7 →
      Trace (compiled (CounterForPrograms.testCmd p) p.counter p.counter) prefixSteps
        (a.withPC (some (compiled (CounterForPrograms.testCmd p) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    have hb : dataBits (a.withPC
        (some (compiled (CounterForPrograms.testCmd p) p.counter p.counter).entry)) ≤
        S * boundaryBound := StreamResources.dataBits_le_mul _ hinitial
    have hc := hinitial p.counter
    have h := StructuredSpace.local_stack_bound
      (compiled (CounterForPrograms.testCmd p) p.counter p.counter)
      (steps := 8 * boundaryBound + 7) hb prefixSteps intermediate (by omega) htrace i
    exact h.trans (by
      simpa only [bound, Nat.add_assoc] using
        (Nat.le_max_right loopBound (S * boundaryBound + 8 * boundaryBound + 7)))
  have hloop' : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter) prefixSteps
        ((CounterForPrograms.testResult p a).withPC
          (some (compiled (CounterForPrograms.loopCmd p body) p.counter p.counter).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
    intro prefixSteps intermediate hle htrace i
    exact (hloop prefixSteps intermediate hle htrace i).trans (Nat.le_max_left _ _)
  have hseq := StructuredSpace.sequence_stack_bound htest hvis.eval p.counter p.counter
    hprefix hloop' (CounterForPrograms.program p body p.counter p.counter)
    (siteAddress (CounterForPrograms.forCmd p body))
    (exitAddress (CounterForPrograms.forCmd p body)) (compiled_site _ p.counter p.counter)
  exact StructuredSpace.compiled_halt_stack_bound (.seq htest hvis.eval)
    p.counter p.counter hseq


/-- A completed actual traversal resets every payload bit while retaining all
record widths. This lets successive scans reuse the same counter frame. -/
theorem visits_reset_counter {R S : ℕ} {p : CounterForPrograms.Ports R S}
    {body : StructuredCalls.Cmd R S} {shape ranks : List ℕ} {steps : ℕ}
    {a b : StructuredCalls.State R S} (h : Visits p body shape ranks steps a b)
    (hstart : a.regs (p.register 2) = true) :
    b.stacks p.counter = Encoding.encodeList id
      (shape.map (fun width => List.replicate width false)) := by
  have hflat : (shape.map (fun width => List.replicate width false)).flatten =
      List.replicate shape.sum false := by
    clear h hstart
    induction shape with
    | nil => rfl
    | cons width shape ih => simp [ih]
  have haux : (a.regs (p.register 2) = false → a.stacks p.counter =
      Encoding.encodeList id (shape.map (fun width => List.replicate width false))) →
      b.stacks p.counter = Encoding.encodeList id
        (shape.map (fun width => List.replicate width false)) := by
    clear hstart
    induction h with
    | done a hf => exact fun hz => hz hf
    | @step words a middle b nb na nt ranks hf hw hc hb he ha tail ih =>
        intro _
        apply ih
        intro hfalse
        have hcarry : (ExecCNFTupleOdometer.bumpWords words).1 = true := by
          simpa only [advanceResult_flag, Bool.not_eq_false_eq_eq_true] using hfalse
        have hv := ExecCNFTupleOdometer.bumpWords_value words
        simp only [hcarry, ite_true] at hv
        have hlt := ExecCNFTupleOdometer.value_lt_power_length words.flatten
        have hz : CounterPrograms.value
            (ExecCNFTupleOdometer.bumpWords words).2.flatten = 0 := by omega
        rw [advanceResult_counter]
        apply congrArg (Encoding.encodeList id)
        apply tuple_eq_of_shape_value
        · simpa only [ExecCNFTupleOdometer.bumpWords_lengths, List.map_map,
            Function.comp_def, List.length_replicate, List.map_id'] using hw
        · simpa only [hflat, value_replicate_false] using hz
  apply haux
  intro hfalse
  simp only [hstart, Bool.true_eq_false] at hfalse

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators
