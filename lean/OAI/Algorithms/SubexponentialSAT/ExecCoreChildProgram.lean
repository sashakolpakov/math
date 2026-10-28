import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecClauseSelfFilterProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScanEncoding
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram

namespace OAI.Algorithms

/-!
# Actual encoded construction of the core child

The caller supplies a forward encoded core clause on stack 9, an encoded
selected family on stack 12, and the parent formula on stack 13. All other
stacks are empty. The program builds the core record, removes every clause
equivalent to a selected clause, restores record order, and calls the concrete
absorber. The result is on stack 13; every other stack is empty.

The finite program does not depend on any of its three input values. The
equivalence tests, framing, reversal, and absorption are actual bit programs.
-/

namespace SubexponentialSAT.ExecCoreChildProgram

open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram


abbrev seedCore : Cmd 15 16 :=
  .seq (transfer 9 15) (.seq (pushFalse 14)
    (.seq (.base (.atom (.set 14 true))) emit))

def seedRegs (regs : Regs) : Regs :=
  flags (Function.update (Function.update (reset regs) 0 false) 14 true)
    false true false

/-- Construct a singleton encoded list by moving and escaping the actual
core payload. Neither the payload nor its length appears in finite control. -/
theorem seedCore_eval (regs : Regs) (bits master source : List Bool) :
    Eval seedCore (8 * bits.length + 18)
      (state regs bits [] master source [] [])
      (state (seedRegs regs) [] [] master source
        (Encoding.encodeList id [bits]) []) := by
  let r := Function.update (reset regs) 0 false
  have hset : Eval (.base (.atom (.set 14 true))) 1
      (state r [] [] master source [false] bits.reverse)
      (state (Function.update r 14 true) [] [] master source [false] bits.reverse) :=
    .base (.atom _ _)
  have hemit := emit_eval (Function.update r 14 true) bits master source [false]
  simp only [Function.update_self, ite_true] at hemit
  have hfull := (transfer_from_query regs bits master source []).seq
    ((pushOutput_eval (reset regs) master source [] bits.reverse).seq (hset.seq hemit))
  have hcost : 3 * bits.length + 3 + (2 + (1 + (5 * bits.length + 11 + 1))) =
      8 * bits.length + 18 := by omega
  simpa only [seedCore, seedRegs, r, SubexpNormalizeProgram.emitIfSelectedSteps,
    ite_true, Encoding.encodeList, id_eq, hcost] using hfull

/-- Finish an actual filter pass with an already encoded output accumulator.
The caller can put reversed petal records in the accumulator as well as the
singleton core used below. -/
abbrev eraseWithAccumulator : Cmd 15 16 :=
  .seq (filterScan .equivalent) (.seq (clear 12)
    (.seq (pushFalse 13) ExecClauseFilterReverse.command))

theorem encoded_append_length_le (xs ys : List (List Bool)) :
    (Encoding.encodeList id (xs ++ ys)).length ≤
      (Encoding.encodeList id xs).length + (Encoding.encodeList id ys).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, Encoding.length_encodeList_cons]
    omega

/-- This shared erasure block accepts any genuine encoded record accumulator.
Its bound counts the accumulator bits, even if none of the parent clauses is
retained. Every payload, including an empty payload, is copied by real loops. -/
theorem eraseWithAccumulator_eval (master F : Formula) (acc : List (List Bool)) (regs : Regs) :
    ∃ n ≤ 999 * ((encodeFormula master).length + (encodeFormula F).length +
        (Encoding.encodeList id acc).length + 1) ^ 2, ∃ rf : Regs,
      Eval eraseWithAccumulator n
        (state regs [] [] (encodeFormula master) (encodeFormula F)
          (Encoding.encodeList id acc) [])
        (state rf [] [] [] (Encoding.encodeList id
          (acc.reverse ++ formulaRecords (filtered .equivalent master F))) [] []) := by
  obtain ⟨n, hn, rf, hscan⟩ := filterScan_eval .equivalent master F acc regs
  let finalRegs := Function.update (reset rf) 0 false
  let records := (formulaRecords (filtered .equivalent master F)).reverse ++ acc
  obtain ⟨m, hm, hreverse⟩ := ExecClauseFilterReverse.reverse_eval records [] finalRegs
  change Eval ExecClauseFilterReverse.command m
    (state finalRegs [] [] [] (Encoding.encodeList id []) (Encoding.encodeList id records) [])
    (state (flags finalRegs false true false) [] [] []
      (Encoding.encodeList id (records.reverse ++ [])) [] []) at hreverse
  have hrecords : records.reverse ++ [] =
      acc.reverse ++ formulaRecords (filtered .equivalent master F) := by
    simp [records]
  rw [hrecords] at hreverse
  have hlength : (Encoding.encodeList id records).length ≤
      (encodeFormula F).length + (Encoding.encodeList id acc).length := by
    calc
      _ ≤ (Encoding.encodeList id (formulaRecords (filtered .equivalent master F)).reverse).length +
          (Encoding.encodeList id acc).length := encoded_append_length_le _ _
      _ = (encodeFormula (filtered .equivalent master F)).length +
          (Encoding.encodeList id acc).length := by rw [encoded_reverse_length, ← encodeFormula_records]
      _ ≤ _ := Nat.add_le_add_right (filtered_length_le .equivalent master F) _
  have hfull := hscan.seq
    ((clearMaster_eval rf (encodeFormula master) [] (Encoding.encodeList id records) []).seq
      ((pushSource_eval (reset rf) [] [] (Encoding.encodeList id records) []).seq hreverse))
  refine ⟨_, ?_, flags finalRegs false true false, hfull⟩
  nlinarith

/-- Prepare the unabsorbed core child. The singleton core accumulator is
reversed together with the kept records, placing the core first. -/
abbrev prepare : Cmd 15 16 := .seq seedCore eraseWithAccumulator

def volume (master F : Formula) (H : Clause) : ℕ :=
  (encodeFormula master).length + (encodeFormula F).length +
    2 * (encodeClause H).length + 3

theorem prepare_eval (master F : Formula) (H : Clause) (regs : Regs) :
    ∃ n ≤ 999 * (volume master F H) ^ 2, ∃ rf : Regs,
      Eval prepare n
        (state regs (encodeClause H) [] (encodeFormula master) (encodeFormula F) [] [])
        (state rf [] [] [] (encodeFormula (H :: filtered .equivalent master F)) [] []) := by
  obtain ⟨n, hn, rf, hscan⟩ := filterScan_eval .equivalent master F [encodeClause H]
    (seedRegs regs)
  let finalRegs := Function.update (reset rf) 0 false
  let records := (formulaRecords (filtered .equivalent master F)).reverse ++ [encodeClause H]
  obtain ⟨m, hm, hreverse⟩ := ExecClauseFilterReverse.reverse_eval records [] finalRegs
  have hrecords : records.reverse ++ [] =
      formulaRecords (H :: filtered .equivalent master F) := by
    simp [records, formulaRecords]
  change Eval ExecClauseFilterReverse.command m
    (state finalRegs [] [] [] (Encoding.encodeList id []) (Encoding.encodeList id records) [])
    (state (flags finalRegs false true false) [] [] []
      (Encoding.encodeList id (records.reverse ++ [])) [] []) at hreverse
  rw [hrecords, ← encodeFormula_records] at hreverse
  have hrecordLength : (Encoding.encodeList id records).length =
      (encodeFormula (H :: filtered .equivalent master F)).length := by
    have h := congrArg (fun xs => (Encoding.encodeList id xs).length) hrecords
    simpa only [List.append_nil, encoded_reverse_length, ← encodeFormula_records] using h
  rw [hrecordLength] at hm
  have hlength := filtered_length_le .equivalent master F
  have hfull := (seedCore_eval regs (encodeClause H) (encodeFormula master) (encodeFormula F)).seq
    (hscan.seq ((clearMaster_eval rf (encodeFormula master) [] (Encoding.encodeList id records) []).seq
      ((pushSource_eval (reset rf) [] [] (Encoding.encodeList id records) []).seq hreverse)))
  refine ⟨_, ?_, flags finalRegs false true false, hfull⟩
  simp only [encodeFormula, Encoding.length_encodeList_cons] at hm
  change m ≤ 10 * (2 * (encodeClause H).length + 2 +
    (encodeFormula (filtered .equivalent master F)).length) at hm
  dsimp [volume]
  nlinarith

abbrev formulaCode := SubexpNormalizationProgram.formulaCode
abbrev clauseCode := ExecCleanLiteralsProgram.clauseCode

def result {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) : List (List α) :=
  ExecCNF.absorb (H :: ExecCNF.eraseClauses F selected)

def inputVolume (F selected : List (List ℕ)) (H : List ℕ) : ℕ :=
  (formulaCode selected).length + (formulaCode F).length + 2 * (clauseCode H).length + 3

theorem filtered_codes (selected F : List (List ℕ)) :
    filtered .equivalent (ExecClauseRelationScan.codeFormula selected)
      (ExecClauseRelationScan.codeFormula F) =
      ExecClauseRelationScan.codeFormula (ExecCNF.eraseClauses F selected) := by
  simp only [filtered, ExecClauseRelationScan.codeFormula, List.filter_map,
    List.any_map, Function.comp_def, ExecClauseRelationScan.test_codes,
    ExecClauseRelationScan.codeTest, ExecCNF.eraseClauses]
  congr 1
  apply congrArg (fun p : List ℕ → Bool => F.filter p)
  funext C
  apply congrArg Bool.not
  apply congrArg (fun p : List ℕ → Bool => selected.any p)
  funext D
  exact Bool.and_comm _ _

theorem prepare_codes_eval (F selected : List (List ℕ)) (H : List ℕ) (regs : Regs) :
    ∃ n ≤ 999 * (inputVolume F selected H) ^ 2, ∃ rf : Regs,
      Eval prepare n
        (state regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [])
        (state rf [] [] [] (formulaCode (H :: ExecCNF.eraseClauses F selected)) [] []) := by
  obtain ⟨n, hn, rf, he⟩ := prepare_eval (ExecClauseRelationScan.codeFormula selected)
    (ExecClauseRelationScan.codeFormula F) (ExecClauseRelationScan.codeClause H) regs
  rw [filtered_codes] at he
  change Eval prepare n _ (state rf [] [] []
    (encodeFormula (ExecClauseRelationScan.codeFormula
      (H :: ExecCNF.eraseClauses F selected))) [] []) at he
  refine ⟨n, ?_, rf, ?_⟩
  · change n ≤ 999 * ((Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) selected).length +
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F).length +
        2 * (Encoding.encodeList Encoding.encodeNat H).length + 3) ^ 2
    simpa only [volume, ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using hn
  · change Eval prepare n
      (state regs (Encoding.encodeList Encoding.encodeNat H) []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) selected)
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F) [] [])
      (state rf [] [] []
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
          (H :: ExecCNF.eraseClauses F selected)) [] [])
    simpa only [ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using he

theorem prepared_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (H :: ExecCNF.eraseClauses F selected)).length + 1 ≤
      inputVolume F selected H := by
  have h := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at h
  change (Encoding.encodeList clauseCode (H :: ExecCNF.eraseClauses F selected)).length + 1 ≤ _
  rw [Encoding.length_encodeList_cons]
  change 2 * (clauseCode H).length + 2 +
    (formulaCode (ExecCNF.eraseClauses F selected)).length + 1 ≤ _
  unfold inputVolume
  omega

/-- The returned child adds at most the serialized core record to the parent
length. This is independent of list order and duplicate literal encodings. -/
theorem result_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (result F selected H)).length ≤
      (formulaCode F).length + 2 * (clauseCode H).length + 2 := by
  have hfilter := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  have habsorb := ExecCNF.length_encodeList_absorb_le clauseCode
    (H :: ExecCNF.eraseClauses F selected)
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at hfilter
  change (formulaCode (result F selected H)).length ≤
    (Encoding.encodeList clauseCode (H :: ExecCNF.eraseClauses F selected)).length at habsorb
  rw [Encoding.length_encodeList_cons] at habsorb
  change (formulaCode (result F selected H)).length ≤ 2 * (clauseCode H).length + 2 +
    (formulaCode (ExecCNF.eraseClauses F selected)).length at habsorb
  omega

def InputReady (d : Data) : Prop :=
  ∀ i : Fin 16, i ≠ 9 → i ≠ 12 → i ≠ 13 → d.stacks i = []

theorem inputReady_eq_state (d : Data) (hready : InputReady d) :
    d = state d.regs (d.stacks 9) [] (d.stacks 12) (d.stacks 13) [] [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  by_cases h9 : i = 9
  · subst i; rfl
  by_cases h12 : i = 12
  · subst i; rfl
  by_cases h13 : i = 13
  · subst i; rfl
  rw [hready i h9 h12 h13]
  fin_cases i <;> simp_all []

abbrev command : Cmd 15 16 := .seq prepare SubexpNormalizationProgram.absorbCommand

/-- The complete source execution has no assumed semantic callback. It
consumes the core and selected family, returning the exact absorbed child. -/
theorem command_eval (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ n ≤ 3200 * (inputVolume F selected H) ^ 2, ∃ e : Data,
      Eval command n d e ∧ SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) := by
  have hd : d = state d.regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [] := by
    simpa only [hcore, hselected, hsource] using inputReady_eq_state d hready
  obtain ⟨n, hn, rf, hprep⟩ := prepare_codes_eval F selected H d.regs
  let a := state rf [] [] [] (formulaCode (H :: ExecCNF.eraseClauses F selected)) [] []
  obtain ⟨m, hm, e, habsorb, he, hout⟩ :=
    SubexpNormalizationProgram.absorb_eval (H :: ExecCNF.eraseClauses F selected)
      a rfl (state_ready _ _)
  have hm' : m ≤ 2200 * (inputVolume F selected H) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left 2200 (Nat.pow_le_pow_left (prepared_length_le F selected H) 2))
  refine ⟨n + m, by omega, e, ?_, he, hout⟩
  rw [hd]
  exact hprep.seq habsorb

def program := compiled command 13 13

/-- Fixed finite code, with its final halt charged to the same quadratic
bound in the lengths of the three actual encoded inputs. -/
theorem program_runsIn (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ e : Data, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) ∧
      RunsIn program (3300 * (inputVolume F selected H) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hr, ho⟩ := command_eval F selected H d hcore hselected hsource hready
  refine ⟨e, hr, ho, n + 1, ?_, compiled_halt_trace he 13 13⟩
  have hv : 0 < inputVolume F selected H := by unfold inputVolume; omega
  have hp := pow_pos hv 2
  omega

theorem primitive_execution (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ e : Data, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (3300 * (inputVolume F selected H) ^ 2))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, hr, ho, ht⟩ := program_runsIn F selected H d hcore hselected hsource hready
  exact ⟨e, hr, ho, BitProgram.primitive_execution program ht⟩

/-- Set semantics of the exact list output, valid even with reordered or
repeated literals and repeated clauses in any of the supplied lists. -/
theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (result F selected H) =
      (insert (ExecCNF.clauseSet H) (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)).filter
        (fun C => ¬ ∃ D ∈ insert (ExecCNF.clauseSet H)
          (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected), D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_cons,
    ExecCNF.formulaSet_eraseClauses]

theorem result_childA {α : Type*} [DecidableEq α]
    (F : List (List α)) (H : List α) (P : List (List α)) :
    result F (ExecCNF.clauses H P) H = ExecCNF.childA F H P := rfl

theorem result_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (F selected : List (List α)) (H : List α) :
    result (F.map (List.map f)) (selected.map (List.map f)) (H.map f) =
      (result F selected H).map (List.map f) := by
  simp only [result, ExecCNFCodeTransport.eraseClauses_map f hf,
    ← List.map_cons, ExecCNFCodeTransport.absorb_map f hf]

theorem result_childA_set {V : Type*} [DecidableEq V]
    (F : List (List (SAT.Literal V))) (H : List (SAT.Literal V))
    (P : List (List (SAT.Literal V))) :
    ExecCNF.formulaSet (result F (ExecCNF.clauses H P) H) =
      SunflowerBranch.childA (ExecCNF.formulaSet F) (ExecCNF.clauseSet H)
        (ExecCNF.formulaSet P) := ExecCNF.childA_set F H P

/-- A selected family need only have the right clause sets. Literal order in
the gathered clauses need not match the core-then-petal concatenation order. -/
theorem result_childA_set_of_selected {V : Type*} [DecidableEq V]
    (F selected : List (List (SAT.Literal V))) (H : List (SAT.Literal V))
    (P : List (List (SAT.Literal V)))
    (hselected : ExecCNF.formulaSet selected =
      SunflowerBranch.clauses (ExecCNF.clauseSet H) (ExecCNF.formulaSet P)) :
    ExecCNF.formulaSet (result F selected H) =
      SunflowerBranch.childA (ExecCNF.formulaSet F) (ExecCNF.clauseSet H)
        (ExecCNF.formulaSet P) := by
  simpa only [hselected, SunflowerBranch.childA, SAT.absorb] using result_set F selected H

end SubexponentialSAT.ExecCoreChildProgram

end OAI.Algorithms
