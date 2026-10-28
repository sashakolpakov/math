import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationPrefixProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFSemanticHelpers
import OAI.Algorithms.SubexponentialSAT.ExecClauseRelationScan
import OAI.Algorithms.SubexponentialSAT.ExecClauseDedupProgram
import OAI.Algorithms.SubexponentialSAT.ExecClauseSelfFilterProgram
import OAI.Algorithms.SubexponentialSAT.ExecCNFCodeTransport

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

abbrev Data := State 15 16
abbrev formulaCode := SubexpNormalizationPrefixProgram.formulaCode

def bitFields (F : List (List ℕ)) : ExecClauseRelationScan.Formula :=
  F.map (List.map Encoding.encodeNat)

theorem clauseCode_fields (C : List ℕ) :
    ExecClauseRelationScan.encodeClause (C.map Encoding.encodeNat) =
      ExecCleanLiteralsProgram.clauseCode C := by
  induction C with
  | nil => rfl
  | cons c C ih =>
    simpa [ExecClauseRelationScan.encodeClause, ExecCleanLiteralsProgram.clauseCode,
      Encoding.encodeList] using ih

theorem formulaCode_fields (F : List (List ℕ)) :
    ExecClauseRelationScan.encodeFormula (bitFields F) = formulaCode F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
    simpa [ExecClauseRelationScan.encodeFormula, bitFields, formulaCode,
      ExecCleanLiteralsProgram.formulaCode, Encoding.encodeList, clauseCode_fields] using ih

def removeSupersets (F : List (List ℕ)) : List (List ℕ) :=
  F.filter fun C => !(F.any fun D => ExecCNF.strictSubset D C)

theorem removeSupersets_dedup (F : List (List ℕ)) :
    removeSupersets (ExecCNF.dedupClauses F) = ExecCNF.absorb F :=
  (ExecCNF.absorb_eq_filter_dedup F).symm

theorem dedup_length_le (F : List (List ℕ)) :
    (formulaCode (ExecCNF.dedupClauses F)).length ≤ (formulaCode F).length :=
  ExecCNF.length_encodeList_dedupClauses_le _ _

theorem removeSupersets_length_le (F : List (List ℕ)) :
    (formulaCode (removeSupersets F)).length ≤ (formulaCode F).length :=
  Encoding.length_encodeList_filter_le _ _ _

theorem normalize_length_le (F : List (List ℕ)) :
    (formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F)).length ≤
      (formulaCode F).length :=
  (ExecCNF.length_encodeList_absorb_le _ _).trans
    (SubexpNormalizationPrefixProgram.preprocess_length_le F)

def Ready (d : Data) : Prop := ∀ i : Fin 16, i ≠ 13 → d.stacks i = []

def prefixRegister (i : Fin 13) : Fin 15 := Fin.castAdd 2 i
def prefixStack (i : Fin 11) : Fin 16 := ⟨13 - i.val, by omega⟩

theorem prefixRegister_injective : Function.Injective prefixRegister := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 15 => i.val) h)

theorem prefixStack_injective : Function.Injective prefixStack := by
  intro i j h
  apply Fin.ext
  have he := congrArg (fun i : Fin 16 => i.val) h
  simp only [prefixStack] at he
  omega

@[simp] theorem prefixStack_zero : prefixStack 0 = 13 := rfl

private theorem embed_restricted {r s R S : ℕ}
    (reg : Fin r → Fin R) (stk : Fin s → Fin S)
    (hr : Function.Injective reg) (hs : Function.Injective stk)
    (frame : State R S) :
    embedState reg stk frame ⟨frame.regs ∘ reg, frame.stacks ∘ stk⟩ = frame := by
  cases frame with
  | mk regs stackValues =>
    unfold embedState
    congr 1
    · funext i
      by_cases h : ∃ j, reg j = i
      · obtain ⟨j, rfl⟩ := h
        exact hr.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h
    · funext i
      by_cases h : ∃ j, stk j = i
      · obtain ⟨j, rfl⟩ := h
        exact hs.extend_apply _ _ _
      · exact Function.extend_apply' _ _ _ h

def prefixProgram := ProgramLinking.liftProgram
  SubexpNormalizationPrefixProgram.program prefixRegister prefixStack

abbrev prefixCall : Cmd 15 16 := .call prefixProgram

theorem prefixCall_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 1000 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval prefixCall n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (SubexpNormalizationPrefixProgram.preprocess F) := by
  let a : SubexpNormalizationPrefixProgram.Data :=
    ⟨d.regs ∘ prefixRegister, d.stacks ∘ prefixStack⟩
  have ha0 : a.stacks 0 = formulaCode F := hsource
  have ha : SubexpNormalizationPrefixProgram.Ready a := by
    apply (ExecCleanLiteralsProgram.ready_iff a).mpr
    intro i hi
    exact hready (prefixStack i) (fun he => hi (prefixStack_injective he))
  obtain ⟨b, hbready, hbout, n, hn, hbtrace⟩ :=
    SubexpNormalizationPrefixProgram.program_runsIn F a ha0 ha
  let e := embedState prefixRegister prefixStack d b
  have he := eval_call_lifted SubexpNormalizationPrefixProgram.program prefixRegister prefixStack d
    prefixRegister_injective prefixStack_injective hbtrace
  rw [embed_restricted _ _ prefixRegister_injective prefixStack_injective] at he
  refine ⟨n, hn, e, he, ?_, ?_⟩
  · intro i hi
    by_cases hp : ∃ j, prefixStack j = i
    · obtain ⟨j, rfl⟩ := hp
      have hj : j ≠ 0 := by
        intro h
        subst j
        exact hi rfl
      exact (embedState_stack prefixRegister prefixStack d b prefixStack_injective j).trans
        ((ExecCleanLiteralsProgram.ready_iff b).mp hbready j hj)
    · exact (embedState_stack_frame prefixRegister prefixStack d b i hp).trans (hready i hi)
  · exact (embedState_stack prefixRegister prefixStack d b prefixStack_injective 0).trans hbout

abbrev dedupCall : Cmd 15 16 := .call ExecClauseDedupProgram.program

theorem dedupCall_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 1200 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval dedupCall n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.dedupClauses F) := by
  obtain ⟨e, he, hout, n, hn, ht⟩ := ExecClauseDedupProgram.program_runsIn F d hsource hready
  exact ⟨n, hn, e, .call _ ht, he, hout⟩

theorem filtered_fields (F : List (List ℕ)) :
    ExecClauseFiltersProgram.filtered .strictSubset (bitFields F) (bitFields F) =
      bitFields (removeSupersets F) := by
  simp only [ExecClauseFiltersProgram.filtered, bitFields, removeSupersets,
    List.filter_map, List.any_map, Function.comp_def, ExecClauseRelationScan.test,
    ExecCNFCodeTransport.strictSubset_map Encoding.encodeNat Encoding.encodeNat_injective]

abbrev removeSupersetsCall : Cmd 15 16 :=
  .call (ExecClauseFiltersProgram.selfFilterProgram .strictSubset)

theorem removeSupersetsCall_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 1000 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval removeSupersetsCall n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (removeSupersets F) := by
  have hs : d.stacks 13 = ExecClauseRelationScan.encodeFormula (bitFields F) := by
    simpa only [formulaCode_fields] using hsource
  obtain ⟨e, he, hout, n, hn, ht⟩ :=
    ExecClauseFiltersProgram.selfFilter_runsIn .strictSubset (bitFields F) d hs hready
  rw [filtered_fields, formulaCode_fields] at hout
  rw [formulaCode_fields] at hn
  exact ⟨n, hn, e, .call _ ht, he, hout⟩

/-- This subroutine is also used after constructing a sparsifier child. -/
abbrev absorbCommand : Cmd 15 16 := .seq dedupCall removeSupersetsCall

theorem absorb_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 2200 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval absorbCommand n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.absorb F) := by
  obtain ⟨n, hn, a, hdup, ha, haout⟩ := dedupCall_eval F d hsource hready
  obtain ⟨m, hm, e, hfilter, he, heout⟩ :=
    removeSupersetsCall_eval (ExecCNF.dedupClauses F) a haout ha
  have hm' : m ≤ 1000 * ((formulaCode F).length + 1) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left 1000
      (Nat.pow_le_pow_left (Nat.add_le_add_right (dedup_length_le F) 1) 2))
  refine ⟨n + m, by omega, e, hdup.seq hfilter, he, ?_⟩
  simpa only [removeSupersets_dedup] using heout

def absorbProgram := compiled absorbCommand 13 13

theorem absorb_runsIn (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = formulaCode (ExecCNF.absorb F) ∧
      RunsIn absorbProgram (2300 * ((formulaCode F).length + 1) ^ 2)
        (d.withPC (some absorbProgram.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := absorb_eval F d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 13 13⟩
  have hpos : 0 < ((formulaCode F).length + 1) ^ 2 := pow_pos (by omega) _
  omega

/-- The complete program contains only the three checked fixed-control stages. -/
abbrev command : Cmd 15 16 := .seq prefixCall absorbCommand

theorem command_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 3200 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval command n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) := by
  obtain ⟨n, hn, a, hprefix, ha, haout⟩ := prefixCall_eval F d hsource hready
  obtain ⟨m, hm, b, hdup, hb, hbout⟩ :=
    dedupCall_eval (SubexpNormalizationPrefixProgram.preprocess F) a haout ha
  obtain ⟨q, hq, e, hfilter, he, heout⟩ := removeSupersetsCall_eval
    (ExecCNF.dedupClauses (SubexpNormalizationPrefixProgram.preprocess F)) b hbout hb
  have hpre := SubexpNormalizationPrefixProgram.preprocess_length_le F
  have hdupLen := (dedup_length_le (SubexpNormalizationPrefixProgram.preprocess F)).trans hpre
  have hm' : m ≤ 1200 * ((formulaCode F).length + 1) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left 1200
      (Nat.pow_le_pow_left (Nat.add_le_add_right hpre 1) 2))
  have hq' : q ≤ 1000 * ((formulaCode F).length + 1) ^ 2 :=
    hq.trans (Nat.mul_le_mul_left 1000
      (Nat.pow_le_pow_left (Nat.add_le_add_right hdupLen 1) 2))
  refine ⟨n + (m + q), by omega, e, hprefix.seq (hdup.seq hfilter), he, ?_⟩
  simpa only [removeSupersets_dedup, SubexpNormalizationPrefixProgram.preprocess,
    ExecCNF.normalize] using heout

def program := compiled command 13 13

theorem program_runsIn (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) ∧
      RunsIn program (3300 * ((formulaCode F).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := command_eval F d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 13 13⟩
  have hpos : 0 < ((formulaCode F).length + 1) ^ 2 := pow_pos (by omega) _
  omega

def inputData (bits : List Bool) : Data :=
  ⟨fun _ => false, fun i => if i = 13 then bits else []⟩

theorem inputData_ready (bits : List Bool) : Ready (inputData bits) := by
  intro i hi
  simp [inputData, hi]

theorem initial_eq_inputData (bits : List Bool) :
    initial program bits = (inputData bits).withPC (some program.entry) := rfl

/-- The raw input is the encoded clause-list body; the variable-count header
is handled by the separate frontend initializer. -/
theorem raw_input_runsIn (F : List (List ℕ)) :
    ∃ e : Data, Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) ∧
      RunsIn program (3300 * ((formulaCode F).length + 1) ^ 2)
        (initial program (formulaCode F)) (e.withPC none) := by
  obtain ⟨e, he, hout, hrun⟩ := program_runsIn F (inputData (formulaCode F))
    (by simp [inputData]) (inputData_ready _)
  exact ⟨e, he, hout, by simpa only [initial_eq_inputData] using hrun⟩

theorem primitive_execution (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (3300 * ((formulaCode F).length + 1) ^ 2))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := program_runsIn F d hsource hready
  exact ⟨e, he, hout, BitProgram.primitive_execution program hrun⟩

theorem raw_input_primitive (F : List (List ℕ)) :
    ∃ e : Data, Ready e ∧
      e.stacks 13 = formulaCode (ExecCNF.normalize SubexpFrontend.negateCode F) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (3300 * ((formulaCode F).length + 1) ^ 2))
        ((primitive program).init (formulaCode F))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := raw_input_runsIn F
  exact ⟨e, he, hout, by
    simpa only [primitive_initial] using BitProgram.primitive_execution program hrun⟩

/-- Exact ordered refinement to the typed worklist's input, including its
redundant final literal-cleanup pass. No finite-set-only equality is used. -/
theorem typed_program_runsIn {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) (d : Data)
    (hsource : d.stacks 13 = formulaCode (F.map (List.map Encoding.literalCode)))
    (hready : Ready d) :
    ∃ e : Data, Ready e ∧
      e.stacks 13 = formulaCode
        ((ExecSparsifyWorklist.normalizedInput F).map (List.map Encoding.literalCode)) ∧
      RunsIn program (3300 * ((formulaCode (F.map (List.map Encoding.literalCode))).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨e, he, hout, hrun⟩ := program_runsIn (F.map (List.map Encoding.literalCode)) d hsource hready
  rw [← ExecCNFCodeTransport.normalizedInput_literalCode F] at hout
  exact ⟨e, he, hout, hrun⟩

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
