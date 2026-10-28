import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearch
import OAI.Algorithms.SubexponentialSAT.RecordPrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement

namespace OAI.Algorithms

/-!
# Fixed control for the universal-block finite search

The commands in this file scan runtime framed lists. Their finite control
depends on the supplied finite predicate program and fixed ports, never on
the block dimension, field size, or list lengths. Predicate specifications
are measured `StructuredCalls.Eval` contracts for actual finite code.
-/

namespace SubexponentialSAT.Subexp.BlockSearchProgram

open BitProgram StructuredCalls

/-- Negate the predicate-result register using two actual instructions. -/
abbrev negateResult {r s : ℕ} (p : RecordPrograms.Ports r s) : Cmd r s :=
  .ite p.found (RecordPrograms.atom (.set p.found false))
    (RecordPrograms.atom (.set p.found true))

theorem negateResult_eval {r s : ℕ} (p : RecordPrograms.Ports r s) (base : State r s)
    (v pr result : Bool) (src out : List Bool) :
    Eval (negateResult p) 2 (RecordPrograms.state p base v pr result src out)
      (RecordPrograms.state p base v pr (!result) src out) := by
  cases result with
  | false =>
      apply Eval.ite_false (by simp)
      exact RecordPrograms.set_found_eval p base v pr false true src out
  | true =>
      apply Eval.ite_true (by simp)
      exact RecordPrograms.set_found_eval p base v pr true false src out

abbrev anyCommand {r s : ℕ} (p : RecordPrograms.Ports r s) (predicate : Cmd r s) : Cmd r s :=
  RecordPrograms.iterate p predicate

abbrev allCommand {r s : ℕ} (p : RecordPrograms.Ports r s) (predicate : Cmd r s) : Cmd r s :=
  .seq (RecordPrograms.iterate p (.seq predicate (negateResult p))) (negateResult p)

theorem negated_contract {r s : ℕ} (p : RecordPrograms.Ports r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (h : RecordPrograms.CallbackContractOn p predicate test cost invariant valid) :
    RecordPrograms.CallbackContractOn p (.seq predicate (negateResult p))
      (fun bits => !(test bits)) (fun bits => cost bits + 2) invariant valid := by
  intro bits tail base hv hi
  obtain ⟨n, next, hn, hnext, run⟩ := h bits tail base hv hi
  exact ⟨n + 2, next, by dsimp; omega, hnext,
    run.seq (negateResult_eval p next false true (test bits) tail [])⟩

theorem not_any_not (records : List (List Bool)) (test : List Bool → Bool) :
    (!(records.any (fun bits => !(test bits)))) = records.all test := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
      cases ht : test bits <;> simp [ht, ih]

/-- A real short-circuiting universal quantifier over encoded records. -/
theorem allCommand_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractOn p predicate test cost invariant valid)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (v pr result : Bool) :
    ∃ n next, n ≤ 5 + RecordPrograms.budget (fun bits => cost bits + 2) records ∧
      invariant next ∧ Eval (allCommand p predicate) n
        (RecordPrograms.state p base v pr result (ProgramEncoding.encodeRecords records ++ suffix) [])
        (RecordPrograms.state p next false true (records.all test)
          (RecordPrograms.unread (fun bits => !(test bits)) records suffix) []) := by
  obtain ⟨n, next, hn, hnext, run⟩ := RecordPrograms.iterate_run_on p
    (.seq predicate (negateResult p)) (fun bits => !(test bits)) (fun bits => cost bits + 2)
    invariant valid (negated_contract p predicate test cost invariant valid contract)
    records suffix base hrecords hbase v pr result
  refine ⟨n + 2, next, by omega, hnext, ?_⟩
  have hrun := run.seq
    (negateResult_eval p next false true (records.any (fun bits => !(test bits)))
      (RecordPrograms.unread (fun bits => !(test bits)) records suffix) [])
  rw [not_any_not records test] at hrun
  exact hrun

/-- The existential quantifier uses the same measured framed-list iterator. -/
theorem anyCommand_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractOn p predicate test cost invariant valid)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (v pr result : Bool) :
    ∃ n next, n ≤ 3 + RecordPrograms.budget cost records ∧ invariant next ∧
      Eval (anyCommand p predicate) n
        (RecordPrograms.state p base v pr result (ProgramEncoding.encodeRecords records ++ suffix) [])
        (RecordPrograms.state p next false true (records.any test)
          (RecordPrograms.unread test records suffix) []) :=
  RecordPrograms.iterate_run_on p predicate test cost invariant valid contract
    records suffix base hrecords hbase v pr result

/-- The semantic history identifies the successful record stored by a concrete
predicate callback. It does not assume a truth oracle or a chosen witness. -/
theorem selected_of_visits {r s : ℕ} (output : Fin s)
    (test : List Bool → Bool) {records : List (List Bool)} {base next : State r s}
    (h : RecordPrograms.Visits test (fun bits _ b => b.stacks output = bits) records base next)
    (hsuccess : records.any test = true) :
    ∃ bits ∈ records, test bits = true ∧ next.stacks output = bits := by
  induction h with
  | nil base => simp at hsuccess
  | @hit bits rest base next ht he => exact ⟨bits, by simp, ht, he⟩
  | @miss bits rest base middle next ht he history ih =>
      have hr : rest.any test = true := by simpa [ht] using hsuccess
      obtain ⟨bits', hbits', htest, hout⟩ := ih hr
      exact ⟨bits', by simp [hbits'], htest, hout⟩

/-- First-success control, with an actual stored successful payload. -/
theorem searchCommand_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (predicate : Cmd r s) (output : Fin s)
    (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractWithOn p predicate test cost invariant
      (fun bits _ b => b.stacks output = bits) valid)
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (hexists : ∃ bits ∈ records, test bits = true) (v pr result : Bool) :
    ∃ n next bits, n ≤ 3 + RecordPrograms.budget cost records ∧ invariant next ∧
      bits ∈ records ∧ test bits = true ∧ next.stacks output = bits ∧
      Eval (anyCommand p predicate) n
        (RecordPrograms.state p base v pr result (ProgramEncoding.encodeRecords records ++ suffix) [])
        (RecordPrograms.state p next false true true
          (RecordPrograms.unread test records suffix) []) := by
  have hs : records.any test = true := List.any_eq_true.mpr hexists
  obtain ⟨n, next, hn, hnext, history, run⟩ := RecordPrograms.iterate_run_with_on
    p predicate test cost invariant (fun bits _ b => b.stacks output = bits) valid
    contract records suffix base hrecords hbase v pr result
  obtain ⟨bits, hbits, htest, hout⟩ := selected_of_visits output test history hs
  refine ⟨n, next, bits, hn, hnext, hbits, htest, hout, ?_⟩
  simpa only [anyCommand, ProgramEncoding.encodeRecords, hs] using run

/-- The saved enumeration is copied for each quantifier invocation. -/
structure SavedPorts (r s : ℕ) extends RecordPrograms.Ports r s where
  saved : Fin s
  temporary : Fin s
  saved_ne_source : saved ≠ source
  saved_ne_payload : saved ≠ payload
  temporary_ne_source : temporary ≠ source
  temporary_ne_payload : temporary ≠ payload
  saved_ne_temporary : saved ≠ temporary

abbrev savedAllCommand {r s : ℕ} (p : SavedPorts r s) (predicate : Cmd r s) : Cmd r s :=
  .seq (.call (StackRoutines.copyProgram p.saved p.source p.temporary p.tag p.present))
    (.seq (allCommand p.toPorts predicate)
      (.seq (.call (StackRoutines.clearProgram p.source p.tag p.present))
        (RecordPrograms.atom (.set p.present true))))

abbrev savedAnyCommand {r s : ℕ} (p : SavedPorts r s) (predicate : Cmd r s) : Cmd r s :=
  .seq (.call (StackRoutines.copyProgram p.saved p.source p.temporary p.tag p.present))
    (.seq (anyCommand p.toPorts predicate)
      (.seq (.call (StackRoutines.clearProgram p.source p.tag p.present))
        (RecordPrograms.atom (.set p.present true))))

private theorem copy_saved_eval {r s : ℕ} (p : SavedPorts r s) (base : State r s)
    (bits : List Bool) (hs : base.stacks p.saved = bits) (ht : base.stacks p.temporary = [])
    (v pr found : Bool) :
    Eval (.call (StackRoutines.copyProgram p.saved p.source p.temporary p.tag p.present))
      (7 * bits.length + 5)
      (RecordPrograms.state p.toPorts base v pr found [] [])
      (RecordPrograms.state p.toPorts base false false found bits []) := by
  have h := TupleProgram.copy_eval p.saved p.source p.temporary p.tag p.present
    p.saved_ne_source p.saved_ne_temporary p.temporary_ne_source p.tag_ne_present
    (RecordPrograms.state p.toPorts base v pr found [] [])
    (by simpa [RecordPrograms.state, p.temporary_ne_source, p.temporary_ne_payload] using ht)
  have he : (⟨readRegs (RecordPrograms.state p.toPorts base v pr found [] []).regs
      p.tag p.present none,
      StackRoutines.copyStacks p.saved p.source
        (RecordPrograms.state p.toPorts base v pr found [] []).stacks⟩ : State r s) =
      RecordPrograms.state p.toPorts base false false found bits [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hv : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [readRegs, RecordPrograms.state, Function.update_apply,
          p.tag_ne_present, p.found_ne_tag, p.found_ne_present]
    · funext i
      by_cases hi : i = p.source <;> by_cases hp : i = p.payload <;>
        simp_all [StackRoutines.copyStacks, RecordPrograms.state, Function.update_apply,
          p.source_ne_payload, Ne.symm p.source_ne_payload,
          p.saved_ne_source, p.saved_ne_payload]
  rw [he] at h
  simpa [RecordPrograms.state, p.saved_ne_source, p.saved_ne_payload, hs] using h

private theorem clear_source_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (base : State r s) (bits : List Bool) (v pr found : Bool) :
    Eval (.call (StackRoutines.clearProgram p.source p.tag p.present)) (2 * bits.length + 3)
      (RecordPrograms.state p base v pr found bits [])
      (RecordPrograms.state p base false false found [] []) := by
  have h := TupleProgram.clear_eval p.source p.tag p.present
    (RecordPrograms.state p base v pr found bits [])
  have he : (⟨readRegs (RecordPrograms.state p base v pr found bits []).regs p.tag p.present none,
      StackRoutines.clearStacks p.source (RecordPrograms.state p base v pr found bits []).stacks⟩ :
        State r s) = RecordPrograms.state p base false false found [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hv : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [readRegs, RecordPrograms.state, Function.update_apply,
          p.tag_ne_present, p.found_ne_tag, p.found_ne_present]
    · funext i
      by_cases hi : i = p.source <;> by_cases hp : i = p.payload <;>
        simp_all [StackRoutines.clearStacks, RecordPrograms.state, Function.update_apply,
          p.source_ne_payload]
  rw [he] at h
  simpa using h

private theorem set_present_eval {r s : ℕ} (p : RecordPrograms.Ports r s)
    (base : State r s) (v pr found pr' : Bool) (src out : List Bool) :
    Eval (RecordPrograms.atom (.set p.present pr')) 1
      (RecordPrograms.state p base v pr found src out)
      (RecordPrograms.state p base v pr' found src out) := by
  have he : (StructuredProgram.Atom.set p.present pr').eval
      (RecordPrograms.state p base v pr found src out) =
      RecordPrograms.state p base v pr' found src out := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hv : i = p.tag <;> by_cases hp : i = p.present <;> by_cases hf : i = p.found <;>
        simp_all [StructuredProgram.Atom.instr, execInstr,
          RecordPrograms.state, p.found_ne_present,
          p.tag_ne_present, Ne.symm p.tag_ne_present, p.found_ne_tag,
          Ne.symm p.found_ne_tag, Ne.symm p.found_ne_present]
    · rfl
  rw [← he]
  exact .base (.atom _ _)

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (ProgramEncoding.encodeRecords records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread]
  | cons bits records ih =>
      cases h : test bits <;>
        simp [RecordPrograms.unread, h, ProgramEncoding.encodeRecords,
          Encoding.encodeList] at * <;> omega

/-- Repeated universal scans preserve the saved enumeration and consume their
working source even when a failed predicate stops the scan early. -/
theorem savedAllCommand_eval {r s : ℕ} (p : SavedPorts r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractOn p.toPorts predicate test cost invariant valid)
    (records : List (List Bool)) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (hs : base.stacks p.saved = ProgramEncoding.encodeRecords records)
    (ht : base.stacks p.temporary = []) (v pr found : Bool) :
    ∃ n next,
      n ≤ 9 * (ProgramEncoding.encodeRecords records).length +
        RecordPrograms.budget (fun bits => cost bits + 2) records + 14 ∧
      invariant next ∧ Eval (savedAllCommand p predicate) n
        (RecordPrograms.state p.toPorts base v pr found [] [])
        (RecordPrograms.state p.toPorts next false true (records.all test) [] []) := by
  have hcopy := copy_saved_eval p base (ProgramEncoding.encodeRecords records) hs ht v pr found
  obtain ⟨n, next, hn, hnext, hall⟩ := allCommand_eval p.toPorts predicate test cost
    invariant valid contract records [] base hrecords hbase false false found
  simp only [List.append_nil] at hall
  have hclear := clear_source_eval p.toPorts next
    (RecordPrograms.unread (fun bits => !(test bits)) records []) false true (records.all test)
  have hset := set_present_eval p.toPorts next false false (records.all test) true [] []
  refine ⟨_, next, ?_, hnext, hcopy.seq (hall.seq (hclear.seq hset))⟩
  have hl := unread_length_le (fun bits => !(test bits)) records
  omega

theorem savedAnyCommand_eval {r s : ℕ} (p : SavedPorts r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractOn p.toPorts predicate test cost invariant valid)
    (records : List (List Bool)) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (hs : base.stacks p.saved = ProgramEncoding.encodeRecords records)
    (ht : base.stacks p.temporary = []) (v pr found : Bool) :
    ∃ n next,
      n ≤ 9 * (ProgramEncoding.encodeRecords records).length +
        RecordPrograms.budget cost records + 12 ∧
      invariant next ∧ Eval (savedAnyCommand p predicate) n
        (RecordPrograms.state p.toPorts base v pr found [] [])
        (RecordPrograms.state p.toPorts next false true (records.any test) [] []) := by
  have hcopy := copy_saved_eval p base (ProgramEncoding.encodeRecords records) hs ht v pr found
  obtain ⟨n, next, hn, hnext, hany⟩ := anyCommand_eval p.toPorts predicate test cost
    invariant valid contract records [] base hrecords hbase false false found
  simp only [List.append_nil] at hany
  have hclear := clear_source_eval p.toPorts next
    (RecordPrograms.unread test records []) false true (records.any test)
  have hset := set_present_eval p.toPorts next false false (records.any test) true [] []
  refine ⟨_, next, ?_, hnext, hcopy.seq (hany.seq (hclear.seq hset))⟩
  have hl := unread_length_le test records
  omega

theorem savedAnyCommand_eval_with {r s : ℕ} (p : SavedPorts r s)
    (predicate : Cmd r s) (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (effect : List Bool → State r s → State r s → Prop)
    (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractWithOn p.toPorts predicate test cost invariant effect valid)
    (records : List (List Bool)) (base : State r s)
    (hrecords : ∀ bits ∈ records, valid bits) (hbase : invariant base)
    (hs : base.stacks p.saved = ProgramEncoding.encodeRecords records)
    (ht : base.stacks p.temporary = []) (v pr found : Bool) :
    ∃ n next,
      n ≤ 9 * (ProgramEncoding.encodeRecords records).length +
        RecordPrograms.budget cost records + 12 ∧ invariant next ∧
      RecordPrograms.Visits test effect records base next ∧
      Eval (savedAnyCommand p predicate) n
        (RecordPrograms.state p.toPorts base v pr found [] [])
        (RecordPrograms.state p.toPorts next false true (records.any test) [] []) := by
  have hcopy := copy_saved_eval p base (ProgramEncoding.encodeRecords records) hs ht v pr found
  obtain ⟨n, next, hn, hnext, history, hany⟩ := RecordPrograms.iterate_run_with_on
    p.toPorts predicate test cost invariant effect valid contract records [] base
    hrecords hbase false false found
  simp only [List.append_nil] at hany
  have hclear := clear_source_eval p.toPorts next
    (RecordPrograms.unread test records []) false true (records.any test)
  have hset := set_present_eval p.toPorts next false false (records.any test) true [] []
  refine ⟨_, next, ?_, hnext, history, hcopy.seq (hany.seq (hclear.seq hset))⟩
  have hl := unread_length_le test records
  omega

/-! A full-dimensional candidate needs only universal scalar tests. -/

open scoped BigOperators
open BlockSearch SubexponentialSAT.QuarticSearch

section Algebra

variable {K : Type*} [Field K] [DecidableEq K]

def pairLinear {N : ℕ} (c : Candidate K N × Candidate K N) :
    ((Fin c.1.1.val → K) × (Fin c.2.1.val → K)) →ₗ[K] Vec K N :=
  (combineLinear c.1).coprod (combineLinear c.2)

omit [DecidableEq K] in
@[simp] theorem pairLinear_apply {N : ℕ} (c : Candidate K N × Candidate K N)
    (ab : (Fin c.1.1.val → K) × (Fin c.2.1.val → K)) :
    pairLinear c ab = combine c.1 ab.1 + combine c.2 ab.2 := rfl

/-- Two concrete matrix-vector products and three zero comparisons suffice
for one coefficient tuple. -/
def coefficientTest {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N × Candidate K N)
    (a : Fin c.1.1.val → K) (b : Fin c.2.1.val → K) : Bool :=
  let y := combine c.1 a + combine c.2 b
  (if y = 0 then decide (a = 0 ∧ b = 0) else true) &&
    decide (matrixMap M y = 0 ↔ b = 0)

/-- An equivalent complete finite checker that replaces the nested spanning
search by injectivity between spaces of the same dimension. -/
def fullPairTest (alphabet : List K) {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N × Candidate K N) : Bool :=
  decide (c.1.1.val + c.2.1.val = N) &&
    (vectors alphabet c.1.1.val).all (fun a =>
      (vectors alphabet c.2.1.val).all (fun b => coefficientTest M c a b))

def FullPairProperty {m N : ℕ} (M : Fin m → Fin N → K)
    (c : Candidate K N × Candidate K N) : Prop :=
  c.1.1.val + c.2.1.val = N ∧
  (∀ a b, combine c.1 a + combine c.2 b = 0 → a = 0 ∧ b = 0) ∧
  (∀ a b, matrixMap M (combine c.1 a + combine c.2 b) = 0 ↔ b = 0)

theorem fullPairTest_iff (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N) :
    fullPairTest alphabet M c = true ↔ FullPairProperty M c := by
  simp only [fullPairTest, coefficientTest, Bool.and_eq_true, decide_eq_true_eq,
    all_vectors_iff alphabet hc, FullPairProperty]
  constructor
  · rintro ⟨hd, h⟩
    refine ⟨hd, ?_, ?_⟩
    · intro a b hz
      have h' := (h a b).1
      simpa [hz] using h'
    · exact fun a b => (h a b).2
  · rintro ⟨hd, hind, hker⟩
    refine ⟨hd, fun a b => ⟨?_, hker a b⟩⟩
    by_cases hz : combine c.1 a + combine c.2 b = 0
    · simpa only [hz, ↓reduceIte, decide_eq_true_eq] using hind a b hz
    · simp [hz]

omit [DecidableEq K] in
theorem FullPairProperty.goodPair {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (h : FullPairProperty M c) : GoodPair M c := by
  rcases h with ⟨hd, hind, hker⟩
  have hinj : Function.Injective (pairLinear c) := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro ab hab
    have hz : combine c.1 ab.1 + combine c.2 ab.2 = 0 := hab
    exact Prod.ext (hind ab.1 ab.2 hz).1 (hind ab.1 ab.2 hz).2
  have hdim : Module.finrank K ((Fin c.1.1.val → K) × (Fin c.2.1.val → K)) =
      Module.finrank K (Vec K N) := by
    simpa [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] using hd
  have hsurj : Function.Surjective (pairLinear c) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨⟨?_, ?_, ?_⟩, hind, ?_⟩
  · intro a ha
    exact (hind a 0 (by simpa using ha)).1
  · intro i
    have hk := (hker (Pi.single i 1) 0).mpr rfl
    simpa [combine, Pi.single_apply, Finset.sum_ite_eq'] using hk
  · intro x hx
    obtain ⟨⟨a, b⟩, hab⟩ := hsurj x
    have hb : b = 0 := (hker a b).mp (by simpa only [← hab, pairLinear_apply] using hx)
    refine ⟨a, ?_⟩
    simpa only [pairLinear_apply, hb, combine_zero, add_zero] using hab
  · intro x
    obtain ⟨⟨a, b⟩, hab⟩ := hsurj x
    exact ⟨a, b, hab⟩

omit [DecidableEq K] in
theorem GoodPair.fullPairProperty {m N : ℕ} {M : Fin m → Fin N → K}
    {c : Candidate K N × Candidate K N} (h : GoodPair M c) : FullPairProperty M c := by
  have hdim := Submodule.finrank_add_eq_of_isCompl h.isCompl
  rw [h.1.finrank_kernel, h.finrank_complement, Module.finrank_pi, Fintype.card_fin] at hdim
  refine ⟨hdim, h.2.1, ?_⟩
  intro a b
  constructor
  · intro hz
    obtain ⟨a', ha'⟩ := h.1.2.2 (combine c.1 a + combine c.2 b) hz
    have heq : combine c.1 (a - a') + combine c.2 b = 0 := by
      rw [combine_sub, ha']
      abel
    exact (h.2.1 (a - a') b heq).2
  · intro hb
    subst b
    simp [combine, map_sum, map_smul, h.1.2.1]

theorem fullPairTest_iff_goodPair (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N) :
    fullPairTest alphabet M c = true ↔ GoodPair M c :=
  (fullPairTest_iff alphabet hc M c).trans ⟨FullPairProperty.goodPair, GoodPair.fullPairProperty⟩

theorem fullPairTest_exists (alphabet : List K) (hc : ∀ a, a ∈ alphabet)
    {m N : ℕ} (M : Fin m → Fin N → K) :
    ∃ c ∈ (candidates alphabet N).product (candidates alphabet N),
      fullPairTest alphabet M c = true := by
  obtain ⟨c, h⟩ := exists_goodPair M
  exact ⟨c, List.mem_product.mpr ⟨mem_candidates alphabet hc c.1, mem_candidates alphabet hc c.2⟩,
    (fullPairTest_iff_goodPair alphabet hc M c).mpr h⟩

/-- A scalar frame is itself a fixed-width injective token for the tuple
generator. Its payload still uses the supplied field-word representation. -/
def framedCode (code : StackEncoding.BlockCode K) : StackEncoding.BlockCode K where
  width := 2 * code.width + 1
  width_pos := by omega
  block a := Encoding.frame (code.block a)
  length_block a := by simp [code.length_block]
  injective_block := by
    intro a b h
    apply code.injective_block
    exact (Encoding.frame_append_injective (rest := []) (rest' := []) (by simpa using h)).1

def coefficientRecords (code : StackEncoding.BlockCode K) (alphabet : List K)
    {N : ℕ} (c : Candidate K N × Candidate K N) : List (List Bool) :=
  TupleProgram.powerRows (alphabet.map code.block) (c.1.1.val + c.2.1.val) [[]]

/-- Every actual generated coefficient payload is tested, with exactly the
same truth condition as quantifying over the two coefficient spaces. -/
theorem coefficientRecords_all_iff (code : StackEncoding.BlockCode K)
    (alphabet : List K) (hc : ∀ a, a ∈ alphabet) {m N : ℕ}
    (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N)
    (test : List Bool → Bool)
    (htest : ∀ a b, test (SubexpTupleRefinement.encodeTuple code a ++
      SubexpTupleRefinement.encodeTuple code b) = coefficientTest M c a b) :
    (coefficientRecords code alphabet c).all test = true ↔
      ∀ a b, coefficientTest M c a b = true := by
  rw [List.all_eq_true]
  constructor
  · intro h a b
    rw [← htest]
    exact h _ (SubexpTupleRefinement.encodePair_mem_powerRows code alphabet hc a b)
  · intro h bits hbits
    obtain ⟨⟨a,b⟩, hab, _⟩ := SubexpTupleRefinement.generated_unique_pair
      code alphabet c.1.1.val c.2.1.val bits hbits
    rw [← hab, htest]
    exact h a b

theorem coefficientRecords_all_iff_goodPair (code : StackEncoding.BlockCode K)
    (alphabet : List K) (hc : ∀ a, a ∈ alphabet) {m N : ℕ}
    (M : Fin m → Fin N → K) (c : Candidate K N × Candidate K N)
    (hdim : c.1.1.val + c.2.1.val = N) (test : List Bool → Bool)
    (htest : ∀ a b, test (SubexpTupleRefinement.encodeTuple code a ++
      SubexpTupleRefinement.encodeTuple code b) = coefficientTest M c a b) :
    (coefficientRecords code alphabet c).all test = true ↔ GoodPair M c := by
  rw [coefficientRecords_all_iff code alphabet hc M c test htest]
  rw [← fullPairTest_iff_goodPair alphabet hc M c]
  simp only [fullPairTest, hdim, decide_true, Bool.true_and,
    all_vectors_iff alphabet hc]

omit [Field K] [DecidableEq K] in
theorem coefficientRecords_length (code : StackEncoding.BlockCode K) (alphabet : List K)
    {N : ℕ} (c : Candidate K N × Candidate K N)
    (hdim : c.1.1.val + c.2.1.val = N) :
    (coefficientRecords code alphabet c).length = alphabet.length^N := by
  simp [coefficientRecords, TupleProgram.powerRows_length, hdim]

omit [Field K] [DecidableEq K] in
theorem coefficientRecord_length (code : StackEncoding.BlockCode K) (alphabet : List K)
    {N : ℕ} (c : Candidate K N × Candidate K N)
    (hdim : c.1.1.val + c.2.1.val = N) (bits : List Bool)
    (hb : bits ∈ coefficientRecords code alphabet c) : bits.length = N * code.width := by
  obtain ⟨⟨a,b⟩, hab, _⟩ := SubexpTupleRefinement.generated_unique_pair
    code alphabet c.1.1.val c.2.1.val bits hb
  rw [← hab, List.length_append]
  simp only [SubexpTupleRefinement.encodeTuple, StackEncoding.length_encodeDataStack,
    List.length_ofFn, ← Nat.add_mul, hdim]

end Algebra

end SubexponentialSAT.Subexp.BlockSearchProgram

end OAI.Algorithms
