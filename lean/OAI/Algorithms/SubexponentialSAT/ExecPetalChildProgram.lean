import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecPetalFamilyProgram
import OAI.Algorithms.SubexponentialSAT.ExecCoreChildProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFCodeTransport

namespace OAI.Algorithms

/-! Actual construction of the petal child. The core, selected family, and
parent occupy the same three ports as the core-child program. -/
namespace SubexponentialSAT.ExecPetalChildProgram
open BitProgram StructuredCalls
open ExecClauseRelationScan (Clause Formula encodeClause encodeFormula)
open ExecClauseFiltersProgram

def familyReg (i : Fin 13) : Fin 15 := Fin.castAdd 2 i
def familyStack : Fin 12 → Fin 16 := ![0, 15, 14, 1, 2, 3, 4, 5, 6, 7, 8, 9]
theorem familyReg_injective : Function.Injective familyReg := Fin.castAdd_injective 13 2
theorem familyStack_injective : Function.Injective familyStack := by decide

def frame (regs : Regs) (working core selected parent output : List Bool) : Data :=
  ⟨regs, ![working, [], [], [], [], [], [], [], [], core, [], [], selected, parent, output, []]⟩

abbrev familyCall : Cmd 15 16 := .call
  (ProgramLinking.liftProgram ExecPetalFamilyProgram.program familyReg familyStack)

theorem familyCall_eval (selected : Formula) (H : Clause) (regs : Regs)
    (master parent : List Bool) :
    ∃ n ≤ 170 * ((encodeClause H).length + 1) * ((encodeFormula selected).length + 1),
      ∃ rf : Regs, Eval familyCall n
        (frame regs (encodeFormula selected) (encodeClause H) master parent [])
        (frame rf [] (encodeClause H) master parent
          (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse)) := by
  let d := frame regs (encodeFormula selected) (encodeClause H) master parent []
  obtain ⟨rf, n, hn, ht⟩ := ExecPetalFamilyProgram.program_runsIn selected H (regs ∘ familyReg)
  let a := ExecPetalFamilyProgram.state (regs ∘ familyReg) (encodeFormula selected) [] [] [] (encodeClause H)
  let b := ExecPetalFamilyProgram.state rf [] []
    (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse) [] (encodeClause H)
  have hstart : embedState familyReg familyStack d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ familyReg_injective familyStack_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have he := eval_call_lifted ExecPetalFamilyProgram.program familyReg familyStack d
    familyReg_injective familyStack_injective ht
  change Eval familyCall n (embedState familyReg familyStack d a)
    (embedState familyReg familyStack d b) at he
  rw [hstart] at he
  let e := embedState familyReg familyStack d b
  have hs (i : Fin 12) : e.stacks (familyStack i) = b.stacks i :=
    embedState_stack _ _ _ _ familyStack_injective i
  have h10 : e.stacks 10 = [] := embedState_stack_frame _ _ _ _ _ (by decide)
  have h11 : e.stacks 11 = [] := embedState_stack_frame _ _ _ _ _ (by decide)
  have h12 : e.stacks 12 = master := embedState_stack_frame _ _ _ _ _ (by decide)
  have h13 : e.stacks 13 = parent := embedState_stack_frame _ _ _ _ _ (by decide)
  have heq : e = frame e.regs [] (encodeClause H) master parent
      (Encoding.encodeList id (formulaRecords (ExecPetalFamilyProgram.petals selected H)).reverse) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · exact hs 0
    · exact hs 3
    · exact hs 4
    · exact hs 5
    · exact hs 6
    · exact hs 7
    · exact hs 8
    · exact hs 9
    · exact hs 10
    · exact hs 11
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact hs 2
    · exact hs 1
  exact ⟨n, hn, e.regs, heq ▸ he⟩

abbrev copySelected : Cmd 15 16 := .call (StackRoutines.copyProgram 12 0 10 0 1)

theorem copySelected_eval (regs : Regs) (core selected parent : List Bool) :
    Eval copySelected (7 * selected.length + 5)
      (frame regs [] core selected parent [])
      (frame (readRegs regs 0 1 none) selected core selected parent []) := by
  have h := ListRegisterProgram.copy_run (r := 15) (s := 16) 12 0 10 0 1
    (by decide) (by decide) (by decide) (by decide) regs
    (frame regs [] core selected parent []).stacks rfl
  have hs : StackRoutines.copyStacks 12 0 (frame regs [] core selected parent []).stacks =
      (frame (readRegs regs 0 1 none) selected core selected parent []).stacks := by
    funext i
    fin_cases i <;> simp [frame, StackRoutines.copyStacks]
  rw [show (frame regs [] core selected parent []).stacks 12 = selected by rfl] at h
  rw [hs] at h
  exact Eval.call _ (by
    simpa only [ListRegisterProgram.Run, StructuredProgram.State.withPC, frame] using h)

theorem clearCore_eval (regs : Regs) (core selected parent output : List Bool) :
    Eval (clear 9) (2 * core.length + 3)
      (state regs core [] selected parent output [])
      (state (reset regs) [] [] selected parent output []) := by
  have h := clear_eval 9 (state regs core [] selected parent output [])
  have heq : cleared 9 (state regs core [] selected parent output []) =
      state (reset regs) [] [] selected parent output [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [state, StackRoutines.clearStacks]
  change Eval (clear 9) (2 * core.length + 3)
    (state regs core [] selected parent output []) _ at h
  rw [heq] at h
  exact h

def petals {α : Type*} [DecidableEq α] (selected : List (List α)) (H : List α) : List (List α) :=
  selected.map (fun C => ExecPetalProgram.result C H)

theorem petals_length_le (selected : Formula) (H : Clause) :
    (encodeFormula (petals selected H)).length ≤ (encodeFormula selected).length := by
  induction selected with
  | nil => exact le_rfl
  | cons C F ih =>
    have hc := ExecPetalProgram.result_encoded_length_le id C H
    change (encodeClause (ExecPetalProgram.result C H)).length ≤ (encodeClause C).length at hc
    simp only [petals, List.map_cons, encodeFormula, Encoding.length_encodeList_cons] at ih ⊢
    omega

abbrev prepare : Cmd 15 16 :=
  .seq copySelected (.seq familyCall (.seq (clear 9) ExecCoreChildProgram.eraseWithAccumulator))

def volume (F selected : Formula) (H : Clause) : ℕ :=
  (encodeFormula selected).length + (encodeFormula F).length + 2 * (encodeClause H).length + 3

theorem prepare_eval (F selected : Formula) (H : Clause) (regs : Regs) :
    ∃ n ≤ 6000 * (volume F selected H)^2, ∃ rf : Regs,
      Eval prepare n (state regs (encodeClause H) [] (encodeFormula selected) (encodeFormula F) [] [])
        (state rf [] [] []
          (encodeFormula (petals selected H ++ filtered .equivalent selected F)) [] []) := by
  obtain ⟨n, hn, rf, hf⟩ := familyCall_eval selected H (readRegs regs 0 1 none)
    (encodeFormula selected) (encodeFormula F)
  let acc := (formulaRecords (petals selected H)).reverse
  obtain ⟨m, hm, final, he⟩ := ExecCoreChildProgram.eraseWithAccumulator_eval
    selected F acc (reset rf)
  have hresult : acc.reverse ++ formulaRecords (filtered .equivalent selected F) =
      formulaRecords (petals selected H ++ filtered .equivalent selected F) := by
    simp [acc, formulaRecords]
  rw [hresult, ← encodeFormula_records] at he
  have hacc : (Encoding.encodeList id acc).length = (encodeFormula (petals selected H)).length := by
    simp only [acc, encoded_reverse_length, ← encodeFormula_records]
  have hp := petals_length_le selected H
  have hvolume : (encodeFormula selected).length + (encodeFormula F).length +
      (Encoding.encodeList id acc).length + 1 ≤ 2 * volume F selected H := by
    rw [hacc]
    dsimp [volume]
    omega
  have hm' : m ≤ 3996 * (volume F selected H)^2 := by
    apply hm.trans
    calc
      _ ≤ 999 * (2 * volume F selected H)^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hvolume 2)
      _ = _ := by ring
  refine ⟨(7 * (encodeFormula selected).length + 5) +
    (n + ((2 * (encodeClause H).length + 3) + m)), ?_, final, ?_⟩
  · dsimp [volume] at *
    nlinarith
  · exact (copySelected_eval regs (encodeClause H) (encodeFormula selected) (encodeFormula F)).seq
      (hf.seq ((clearCore_eval rf (encodeClause H) (encodeFormula selected)
        (encodeFormula F) (Encoding.encodeList id acc)).seq he))

abbrev formulaCode := SubexpNormalizationProgram.formulaCode
abbrev clauseCode := ExecCleanLiteralsProgram.clauseCode

theorem formulaCode_encoding (F : List (List ℕ)) :
    formulaCode F = Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) F := by
  rw [← ExecClauseRelationScan.encodeFormula_codes]
  exact (SubexpNormalizationProgram.formulaCode_fields F).symm

def result {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) : List (List α) :=
  ExecCNF.absorb (petals selected H ++ ExecCNF.eraseClauses F selected)

def inputVolume (F selected : List (List ℕ)) (H : List ℕ) : ℕ :=
  (formulaCode selected).length + (formulaCode F).length + 2 * (clauseCode H).length + 3

theorem petals_codes (selected : List (List ℕ)) (H : List ℕ) :
    petals (ExecClauseRelationScan.codeFormula selected) (ExecClauseRelationScan.codeClause H) =
      ExecClauseRelationScan.codeFormula (petals selected H) := by
  simpa [petals, ExecPetalProgram.result, ExecClauseRelationScan.codeFormula,
    ExecClauseRelationScan.codeClause] using
    ExecCNFCodeTransport.petal_family_map Encoding.encodeNat Encoding.encodeNat_injective selected H

theorem prepare_codes_eval (F selected : List (List ℕ)) (H : List ℕ) (regs : Regs) :
    ∃ n ≤ 6000 * (inputVolume F selected H)^2, ∃ rf : Regs,
      Eval prepare n (state regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [])
        (state rf [] [] [] (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)) [] []) := by
  obtain ⟨n, hn, rf, he⟩ := prepare_eval (ExecClauseRelationScan.codeFormula F)
    (ExecClauseRelationScan.codeFormula selected) (ExecClauseRelationScan.codeClause H) regs
  rw [petals_codes, ExecCoreChildProgram.filtered_codes] at he
  have happend : ExecClauseRelationScan.codeFormula (petals selected H) ++
      ExecClauseRelationScan.codeFormula (ExecCNF.eraseClauses F selected) =
      ExecClauseRelationScan.codeFormula (petals selected H ++ ExecCNF.eraseClauses F selected) := by
    simp [ExecClauseRelationScan.codeFormula]
  rw [happend] at he
  refine ⟨n, ?_, rf, ?_⟩
  · simpa [volume, inputVolume, formulaCode_encoding, clauseCode,
      ExecCleanLiteralsProgram.clauseCode,
      ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using hn
  · simpa only [formulaCode_encoding, ExecCleanLiteralsProgram.clauseCode,
      ExecClauseRelationScan.encodeFormula_codes,
      ExecClauseRelationScan.encodeClause_codes] using he

theorem encode_append_length_le {α : Type*} (enc : α → List Bool) (xs ys : List α) :
    (Encoding.encodeList enc (xs ++ ys)).length ≤
      (Encoding.encodeList enc xs).length + (Encoding.encodeList enc ys).length := by
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons x xs ih =>
    simp only [List.cons_append, Encoding.length_encodeList_cons]
    omega

theorem petals_code_length_le (selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (petals selected H)).length ≤ (formulaCode selected).length := by
  have h := petals_length_le (ExecClauseRelationScan.codeFormula selected)
    (ExecClauseRelationScan.codeClause H)
  simpa only [formulaCode_encoding, petals_codes,
    ExecClauseRelationScan.encodeFormula_codes] using h

theorem prepared_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length + 1 ≤
      inputVolume F selected H := by
  have hp := petals_code_length_le selected H
  have he := Encoding.length_encodeList_filter_le clauseCode
    (fun C => !(selected.any fun D => ExecCNF.equivalent C D)) F
  change (formulaCode (ExecCNF.eraseClauses F selected)).length ≤ (formulaCode F).length at he
  have ha := encode_append_length_le clauseCode (petals selected H) (ExecCNF.eraseClauses F selected)
  change (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length ≤
    (formulaCode (petals selected H)).length + (formulaCode (ExecCNF.eraseClauses F selected)).length at ha
  unfold inputVolume
  omega

theorem result_length_le (F selected : List (List ℕ)) (H : List ℕ) :
    (formulaCode (result F selected H)).length + 1 ≤ inputVolume F selected H := by
  have ha := ExecCNF.length_encodeList_absorb_le clauseCode
    (petals selected H ++ ExecCNF.eraseClauses F selected)
  change (formulaCode (result F selected H)).length ≤
    (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)).length at ha
  exact (Nat.add_le_add_right ha 1).trans (prepared_length_le F selected H)

abbrev InputReady := ExecCoreChildProgram.InputReady
abbrev command : Cmd 15 16 := .seq prepare SubexpNormalizationProgram.absorbCommand

theorem command_eval (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ n ≤ 19000 * (inputVolume F selected H)^2, ∃ e : Data,
      Eval command n d e ∧ SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) := by
  have hd : d = state d.regs (clauseCode H) [] (formulaCode selected) (formulaCode F) [] [] := by
    simpa only [hcore, hselected, hsource] using ExecCoreChildProgram.inputReady_eq_state d hready
  obtain ⟨n, hn, rf, hp⟩ := prepare_codes_eval F selected H d.regs
  let a := state rf [] [] [] (formulaCode (petals selected H ++ ExecCNF.eraseClauses F selected)) [] []
  obtain ⟨m, hm, e, he, hr, ho⟩ := SubexpNormalizationProgram.absorb_eval
    (petals selected H ++ ExecCNF.eraseClauses F selected) a rfl (ExecClauseFiltersProgram.state_ready _ _)
  have hm' : m ≤ 2200 * (inputVolume F selected H)^2 :=
    hm.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (prepared_length_le F selected H) 2))
  refine ⟨n + m, by omega, e, ?_, hr, ho⟩
  rw [hd]
  exact hp.seq he

def program := compiled command 13 13

theorem program_runsIn (F selected : List (List ℕ)) (H : List ℕ) (d : Data)
    (hcore : d.stacks 9 = clauseCode H) (hselected : d.stacks 12 = formulaCode selected)
    (hsource : d.stacks 13 = formulaCode F) (hready : InputReady d) :
    ∃ e : Data, SubexpNormalizationProgram.Ready e ∧
      e.stacks 13 = formulaCode (result F selected H) ∧
      RunsIn program (20000 * (inputVolume F selected H)^2)
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
        (primitiveOverhead program * (20000 * (inputVolume F selected H)^2))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, hr, ho, ht⟩ := program_runsIn F selected H d hcore hselected hsource hready
  exact ⟨e, hr, ho, BitProgram.primitive_execution program ht⟩

theorem petals_set {α : Type*} [DecidableEq α] (selected : List (List α)) (H : List α) :
    ExecCNF.formulaSet (petals selected H) =
      (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H) :=
  ExecCNFCodeTransport.petal_family_set selected H

theorem result_set {α : Type*} [DecidableEq α]
    (F selected : List (List α)) (H : List α) :
    let P := (ExecCNF.formulaSet selected).image (fun C => C \ ExecCNF.clauseSet H)
    let G := P ∪ (ExecCNF.formulaSet F \ ExecCNF.formulaSet selected)
    ExecCNF.formulaSet (result F selected H) = G.filter (fun C => ¬ ∃ D ∈ G, D ⊂ C) := by
  simp only [result, ExecCNF.formulaSet_absorb, ExecCNF.formulaSet_append,
    ExecCNF.formulaSet_eraseClauses, petals_set]

theorem result_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (F selected : List (List α)) (H : List α) :
    result (F.map (List.map f)) (selected.map (List.map f)) (H.map f) =
      (result F selected H).map (List.map f) := by
  have hp : petals (selected.map (List.map f)) (H.map f) =
      (petals selected H).map (List.map f) :=
    ExecCNFCodeTransport.petal_family_map f hf selected H
  simp only [result, hp, ExecCNFCodeTransport.eraseClauses_map f hf,
    ← List.map_append, ExecCNFCodeTransport.absorb_map f hf]

/-- Once the selected clauses and recovered petals are identified with the
chosen sunflower, the actual encoded output has exactly child B's set. -/
theorem result_childB_set {V : Type*} [DecidableEq V]
    (F selected : List (List (SAT.Literal V))) (H : List (SAT.Literal V))
    (P : List (List (SAT.Literal V)))
    (hselected : ExecCNF.formulaSet selected = ExecCNF.formulaSet (ExecCNF.clauses H P))
    (hpetals : ExecCNF.formulaSet (petals selected H) = ExecCNF.formulaSet P) :
    ExecCNF.formulaSet (result F selected H) =
      SunflowerBranch.childB (ExecCNF.formulaSet F) (ExecCNF.clauseSet H) (ExecCNF.formulaSet P) := by
  rw [← ExecCNF.childB_set F H P]
  simp only [result, ExecCNF.childB, ExecCNF.formulaSet_absorb,
    ExecCNF.formulaSet_append, ExecCNF.formulaSet_eraseClauses, hselected, hpetals]
  rw [Finset.union_comm]

end SubexponentialSAT.ExecPetalChildProgram

end OAI.Algorithms
