import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpActualSparsify

namespace OAI.Algorithms

/-!
# The same concrete sparsifier on ordered raw formulas

The input clauses and literals may be in any order and may repeat. The
existing finite normalizer and observed worklist execute unchanged. This
module retains their actual traces and the exact setup words, so the raw-ID
transport needs no separate canonical sorting pass.
-/

namespace SubexponentialSAT.SubexpOrderedRawSparsify

open BitProgram StructuredCalls SubexpMainProgram SubexpProcedureCompose
open SubexpSetupProgram (Config helperSize mainExtraStacks thresholdCount)
open ExecSparsifyWorklist (normalizedInput)

abbrev Data (c : Config) (er : ℕ) := MainState er (mainExtraStacks c)

/-- Keep the actual intermediate execution, so later runtime arguments may
recover the exact raw parameter words in this same state. -/
def NormalizationRun (c : Config) {er n : ℕ} (F : ExecSparsifyObserved.Formula n)
    (caller middle : Data c er) : Prop :=
  ∃ t, t ≤ 3500 * ((ExecSparsifyObserved.encode F).length + 1) ^ 2 ∧
    Eval (SubexpMainNormalization.procedure er (mainExtraStacks c)).invoke t caller middle

def procedure (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    Procedure er (mainExtraStacks c) :=
  SubexpNormalizedSparsify.procedure (SubexpConcreteNode.program c hr)

/-- The instruction table is exactly the canonical-input phase's table. -/
theorem procedure_eq (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    procedure c hr = SubexpActualSparsify.procedure c hr := rfl

/-- Numeric literal payloads agree byte-for-byte with the observed-node ABI. -/
theorem body_code {n : ℕ} (F : ExecSparsifyObserved.Formula n) :
    SubexpNormalizationProgram.formulaCode (F.map (List.map Encoding.literalCode)) =
      ExecSparsifyObserved.encode F :=
  (ExecSparsifyEncoding.words_encoding F).symm

/-- The existing normalizer accepts ordered raw clauses directly. -/
theorem normalize_invoke {er es n : ℕ} (F : ExecSparsifyObserved.Formula n)
    (a : MainState er es)
    (hbody : a.stacks (persistent es 0) = ExecSparsifyObserved.encode F)
    (hwork : SubexpMainNormalization.WorkspaceClean a) :
    ∃ t ≤ 3500 * ((ExecSparsifyObserved.encode F).length + 1) ^ 2,
      ∃ b : MainState er es,
      Eval (SubexpMainNormalization.procedure er es).invoke t a b ∧
      SubexpMainNormalization.WorkspaceClean b ∧
      b.stacks (persistent es 0) = ExecSparsifyObserved.encode (normalizedInput F) ∧
      (∀ i : Fin 32, i ≠ 0 → b.stacks (persistent es i) = a.stacks (persistent es i)) ∧
      (∀ i : Fin 3, b.regs (controlRegister er i) = a.regs (controlRegister er i)) := by
  have hb : a.stacks (persistent es 0) =
      SubexpNormalizationProgram.formulaCode (F.map (List.map Encoding.literalCode)) :=
    hbody.trans (body_code F).symm
  obtain ⟨t, ht, b, he, hw, ho, hf, hc⟩ :=
    SubexpMainNormalization.invoke_eval (F.map (List.map Encoding.literalCode)) a hb hwork
  rw [body_code] at ht
  exact ⟨t, ht, b, he, hw, ho.trans (ExecSparsifyStartup.numeric_normalizedInput_code F), hf, hc⟩

/-- Normalization cannot increase the actual raw body length. -/
theorem normalized_length_le {n : ℕ} (F : ExecSparsifyObserved.Formula n) :
    (ExecSparsifyObserved.encode (normalizedInput F)).length ≤
      (ExecSparsifyObserved.encode F).length := by
  have h := SubexpNormalizationProgram.normalize_length_le
    (F.map (List.map Encoding.literalCode))
  rw [body_code, ExecSparsifyStartup.numeric_normalizedInput_code] at h
  exact h

/-- This frame contains the actual normalizer's output stacks and the
physical reset's all-false work registers. -/
noncomputable def inputFrame (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (middle : Data c er) : SubexpConcreteNode.Frame c er :=
  SubexpSparsifyInput.inputFrame c (SubexpConcreteNode.program c hr) middle
    (ExecSparsifyObserved.encode (normalizedInput F))

theorem thresholds (c : Config) (M : ℕ) (hM : 2 ≤ M) :
    ∀ d, 2 ≤ d → d ≤ c.k → 2 ≤ SparsificationConstants.z M d :=
  fun d hd _ => SparsificationConstants.threshold_ge_two M d hM hd

noncomputable def output (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (M : ℕ) (hM : 2 ≤ M) (middle : Data c er)
    (hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle))
    (hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
      (inputFrame c hr F middle)) : List (ExecSparsifyObserved.Formula n) :=
  (ExecSparsifyWorklist.run
    (SubexpConcreteNode.branching c hr (inputFrame c hr F middle)
      (SparsificationConstants.z M) hf hb (thresholds c M hM))
    (ExecSparsifyWorklist.initial (normalizedInput F))).leaves

noncomputable def result (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (M : ℕ) (hM : 2 ≤ M) (middle : Data c er)
    (hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle))
    (hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
      (inputFrame c hr F middle)) : Data c er :=
  SubexpCanonicalSparsify.result (SubexpConcreteNode.program c hr) middle
    (ExecSparsifyObserved.encode (normalizedInput F))
    (Encoding.encodeList ExecSparsifyObserved.encode (output c hr F M hM middle hf hb))

noncomputable def bound (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (M : ℕ) (hM : 2 ≤ M) (middle : Data c er)
    (hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle))
    (hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
      (inputFrame c hr F middle)) : ℕ :=
  3500 * ((ExecSparsifyObserved.encode F).length + 1) ^ 2 +
    SubexpSparsifyTreeRun.treeBound er ExecSparsifyObserved.encode
      (SubexpConcreteNode.branching c hr (inputFrame c hr F middle)
        (SparsificationConstants.z M) hf hb (thresholds c M hM))
      (SubexpConcreteNode.cost c hr (inputFrame c hr F middle)
        (SparsificationConstants.z M) hf hb (thresholds c M hM))
      (normalizedInput F) + 1

/-- A numerical estimate for the already implemented node changes only the
bound on this execution, not the machine or its semantic output. -/
theorem bound_le (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F)
    (M : ℕ) (hM : 2 ≤ M) (middle : Data c er)
    (hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle))
    (hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
      (inputFrame c hr F middle)) (B : ℕ)
    (hB : ∀ G : ExecSparsifyObserved.Formula n, ExecSparsifyObserved.Ready c.k G →
      SubexpConcreteNode.cost c hr (inputFrame c hr F middle)
        (SparsificationConstants.z M) hf hb (thresholds c M hM) G +
      ExecWorklistLoop.updateCost ExecSparsifyObserved.encode G
        ((SubexpConcreteNode.branching c hr (inputFrame c hr F middle)
          (SparsificationConstants.z M) hf hb (thresholds c M hM)).split G) ≤ B) :
    bound c hr F M hM middle hf hb ≤
      3500 * ((ExecSparsifyObserved.encode F).length + 1) ^ 2 +
        SubexpMainSparsify.runBound ExecSparsifyObserved.encode
          (SubexpConcreteNode.branching c hr (inputFrame c hr F middle)
            (SparsificationConstants.z M) hf hb (thresholds c M hM)) B
          (normalizedInput F) + workRegs er + 3 := by
  have h := SubexpSparsifyTreeRun.treeBound_le er ExecSparsifyObserved.encode
    (SubexpConcreteNode.branching c hr (inputFrame c hr F middle)
      (SparsificationConstants.z M) hf hb (thresholds c M hM))
    (ExecSparsifyObserved.Ready c.k)
    (SubexpConcreteNode.cost c hr (inputFrame c hr F middle)
      (SparsificationConstants.z M) hf hb (thresholds c M hM)) B
    (SubexpConcreteNode.branching_closed c hr _ _ hf hb (thresholds c M hM)) hB
    (normalizedInput F) (ExecSparsifyStartup.normalizedInput_ready F c.k hF)
  unfold bound
  omega

/-- The postcondition concerns the emitted bytes, the original SAT formula,
and the exact physical storage available to the next main phase. -/
structure Outcome (c : Config) {er n : ℕ} (F : ExecSparsifyObserved.Formula n) (M : ℕ)
    (caller final : Data c er) (leaves : List (ExecSparsifyObserved.Formula n)) : Prop where
  body : final.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode (normalizedInput F)
  leaf_stream : final.stacks (persistent (mainExtraStacks c) 7) =
    Encoding.encodeList ExecSparsifyObserved.encode leaves
  correct : ExecEncodedSparsifier.CorrectOutput c.k
    (SparsificationConstants.occurrenceCap M c.k)
    (F) leaves
  persistent_frame : ∀ i : Fin 32, i ≠ 0 → i ≠ 7 →
    final.stacks (persistent (mainExtraStacks c) i) = caller.stacks (persistent (mainExtraStacks c) i)
  control_frame : ∀ i : Fin 3,
    final.regs (controlRegister er i) = caller.regs (controlRegister er i)
  registers : ∀ i : Fin (workRegs er), final.regs (workRegister er i) = false
  workspace : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) final
  threshold_frame : ∀ i : Fin (thresholdCount c),
    final.stacks (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i)) =
      caller.stacks (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i))

theorem Outcome.satisfiable {c : Config} {er n M : ℕ} {F : ExecSparsifyObserved.Formula n}
    {caller final : Data c er} {leaves : List (ExecSparsifyObserved.Formula n)}
    (h : Outcome c F M caller final leaves) :
    SAT.Satisfiable (ExecCNF.formulaSet F) ↔
      ∃ G ∈ leaves, SAT.Satisfiable (ExecCNF.formulaSet G) :=
  h.correct.satisfiable

theorem Outcome.models {c : Config} {er n M : ℕ} {F : ExecSparsifyObserved.Formula n}
    {caller final : Data c er} {leaves : List (ExecSparsifyObserved.Formula n)}
    (h : Outcome c F M caller final leaves) (a : SAT.Assignment (Fin n)) :
    SAT.CNF.eval a (ExecCNF.formulaSet F) = true ↔
      ∃ G ∈ leaves, SAT.CNF.eval a (ExecCNF.formulaSet G) = true :=
  h.correct.models a

/-- The semantic output is the very list emitted by the concrete worklist. -/
theorem output_correct (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F)
    (M : ℕ) (hM : 2 ≤ M) (middle : Data c er)
    (hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle))
    (hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
      (inputFrame c hr F middle)) :
    ExecEncodedSparsifier.CorrectOutput c.k (SparsificationConstants.occurrenceCap M c.k)
      (F) (output c hr F M hM middle hf hb) := by
  have h := ExecEncodedSparsifier.correct_output
    (SubexpConcreteNode.localFrame c hr (inputFrame c hr F middle)) M
    (SubexpConcreteNode.local_ready c hr _ hf)
    (SubexpConcreteNode.local_bank c hr _ _ hb) (thresholds c M hM)
    (normalizedInput F) (ExecSparsifyStartup.normalizedInput_ready F c.k hF) hM
  change ExecEncodedSparsifier.CorrectOutput c.k _ (normalizedInput F)
    (output c hr F M hM middle hf hb) at h
  refine ⟨?_, ?_, h.clause_nodup, h.literal_nodup, h.width, h.occurrence⟩
  · intro a
    simpa only [ExecSparsifyWorklist.normalizedInput_set, SAT.eval_normalize] using h.models a
  · simpa only [SAT.Satisfiable, ExecSparsifyWorklist.normalizedInput_set,
      SAT.eval_normalize] using h.satisfiable

/-- There is no hypothetical splitter premise. The only initialization
premises describe the actual body, empty ordinary workspace, and threshold
words. `from_setup` below obtains these words from the numerical program. -/
theorem invoke_detailed (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F)
    (M : ℕ) (hM : 2 ≤ M) (caller : Data c er)
    (hbody : caller.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode F)
    (hwork : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) caller)
    (hleaves : caller.stacks (persistent (mainExtraStacks c) 7) = [])
    (hbank : ∀ i : Fin (thresholdCount c), BinaryArithmetic.toNat
      (caller.stacks (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i))) =
        SparsificationConstants.z M (i.val + 2)) :
    ∃ middle : Data c er,
    ∃ hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle),
    ∃ hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
        (inputFrame c hr F middle),
    ∃ steps, steps ≤ bound c hr F M hM middle hf hb ∧
      Eval (procedure c hr).invoke steps caller (result c hr F M hM middle hf hb) ∧
      Outcome c F M caller (result c hr F M hM middle hf hb)
        (output c hr F M hM middle hf hb) ∧
      NormalizationRun c F caller middle := by
  have hw : SubexpMainNormalization.WorkspaceClean caller := by
    intro i
    apply hwork
    change i.val < helperSize c
    have := i.isLt
    have := SubexpSetupProgram.helperSize_ge c
    omega
  obtain ⟨tn, htn, middle, hn, hmw, hmb, hmp, hmc⟩ :=
    normalize_invoke F caller hbody hw
  have hprefix : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) middle :=
    SubexpNormalizedSparsify.normalization_empty_prefix hn hmw _
      (by have := SubexpNodePorts.setup_fit c; omega) hwork
  have hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle) :=
    SubexpSparsifyInput.inputFrame_ready c (SubexpConcreteNode.program c hr)
      middle _ hprefix
  have hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
      (inputFrame c hr F middle) := by
    intro i
    change Fin (SubexpSetupProgram.thresholdCount c) at i
    change BinaryArithmetic.toNat ((SubexpSparsifyInput.inputFrame c
      (SubexpConcreteNode.program c hr) middle _).stacks
        (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i))) = _
    rw [SubexpSparsifyInput.inputFrame_threshold]
    rw [SubexpNormalizedSparsify.normalization_high_frame hn _
      (SubexpSparsifyInput.threshold_low c i) (SubexpSparsifyInput.threshold_high c i)]
    exact hbank i
  have hready := SubexpNormalizedSparsify.handoff_ready
    (SubexpConcreteNode.program c hr) middle hmw ((hmp 7 (by decide)).trans hleaves)
  have htyped : middle.stacks (persistent (mainExtraStacks c) 0) =
      ExecSparsifyObserved.encode (normalizedInput F) := hmb
  obtain ⟨ts, hts, hs⟩ := SubexpSparsifyTreeRun.canonical_invoke
    (SubexpConcreteNode.program c hr) middle hready ExecSparsifyObserved.encode
    (SubexpConcreteNode.branching c hr (inputFrame c hr F middle)
      (SparsificationConstants.z M) hf hb (thresholds c M hM))
    (ExecSparsifyObserved.Ready c.k)
    (SubexpConcreteNode.cost c hr (inputFrame c hr F middle)
      (SparsificationConstants.z M) hf hb (thresholds c M hM))
    (normalizedInput F) (ExecSparsifyStartup.normalizedInput_ready F c.k hF) htyped
    (SubexpConcreteNode.branching_closed c hr _ _ hf hb (thresholds c M hM))
    (SubexpConcreteNode.realizes c hr _ _ hf hb (thresholds c M hM))
  refine ⟨middle, hf, hb, tn + ts + 1, ?_, sequence_invoke _ _ hn hs, ?_, ⟨tn, htn, hn⟩⟩
  · unfold bound
    omega
  · constructor
    · exact SubexpNormalizedSparsify.result_body _ middle _ _
    · exact SubexpCanonicalSparsify.leaf_stream _ middle _ _
    · exact output_correct c hr F hF M hM middle hf hb
    · intro i hi0 hi7
      exact (SubexpCanonicalSparsify.preserves_persistent _ middle _ _ i hi0 hi7).trans
        (hmp i hi0)
    · intro i
      exact (SubexpCanonicalSparsify.preserves_control _ middle _ _ i).trans (hmc i)
    · exact SubexpNormalizedSparsify.result_work_register _ middle _ _
    · exact SubexpNormalizedSparsify.result_empty_prefix _ middle _ _ _
        (by have := SubexpNodePorts.setup_fit c; omega) hprefix
    · intro i
      exact (SubexpActualSparsify.canonical_work_frame _ middle _ _ _
        (by have := SubexpSparsifyInput.threshold_low c i; omega)
        (SubexpSparsifyInput.threshold_high c i)).trans
          (SubexpNormalizedSparsify.normalization_high_frame hn _
            (SubexpSparsifyInput.threshold_low c i) (SubexpSparsifyInput.threshold_high c i))

theorem invoke (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F)
    (M : ℕ) (hM : 2 ≤ M) (caller : Data c er)
    (hbody : caller.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode F)
    (hwork : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) caller)
    (hleaves : caller.stacks (persistent (mainExtraStacks c) 7) = [])
    (hbank : ∀ i : Fin (thresholdCount c), BinaryArithmetic.toNat
      (caller.stacks (SubexpSetupProgram.mainStack c (SubexpSetupProgram.threshold c i))) =
        SparsificationConstants.z M (i.val + 2)) :
    ∃ middle : Data c er,
    ∃ hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle),
    ∃ hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z M)
        (inputFrame c hr F middle),
    ∃ steps, steps ≤ bound c hr F M hM middle hf hb ∧
      Eval (procedure c hr).invoke steps caller (result c hr F M hM middle hf hb) ∧
      Outcome c F M caller (result c hr F M hM middle hf hb)
        (output c hr F M hM middle hf hb) := by
  obtain ⟨middle, hf, hb, steps, ht, he, ho, _⟩ :=
    invoke_detailed c hr F hF M hM caller hbody hwork hleaves hbank
  exact ⟨middle, hf, hb, steps, ht, he, ho⟩

/-- The initialization premises of `invoke` follow from the actual numerical
setup, including all protected threshold words. -/
theorem from_setup_detailed (c : Config) {er n setupSteps : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F)
    (before caller : Data c er)
    (hn : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 4)) =
      SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 5)) =
      SubexpPackingParameters.u n)
    (hgood : SubexpPackingParameters.GoodInput n)
    (he : Eval (SubexpSetupProgram.mainProcedure c er).invoke setupSteps before caller)
    (hbody : caller.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode F)
    (hleaves : caller.stacks (persistent (mainExtraStacks c) 7) = []) :
    ∃ middle : Data c er,
    ∃ hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle),
    ∃ hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z (DyadicSchedule.M c.T n))
        (inputFrame c hr F middle),
    ∃ steps, steps ≤ bound c hr F (DyadicSchedule.M c.T n)
        (DyadicSchedule.M_ge_two c.T n) middle hf hb ∧
      Eval (procedure c hr).invoke steps caller
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) ∧
      Outcome c F (DyadicSchedule.M c.T n) caller
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb)
        (output c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) ∧
      NormalizationRun c F caller middle := by
  obtain ⟨hw, _, hbank, _, _⟩ := SubexpSparsifyInput.setup_post c hn hs hu hgood he
  exact invoke_detailed c hr F hF _ (DyadicSchedule.M_ge_two c.T n) caller hbody hw hleaves hbank

theorem from_setup (c : Config) {er n setupSteps : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F)
    (before caller : Data c er)
    (hn : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 4)) =
      SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 5)) =
      SubexpPackingParameters.u n)
    (hgood : SubexpPackingParameters.GoodInput n)
    (he : Eval (SubexpSetupProgram.mainProcedure c er).invoke setupSteps before caller)
    (hbody : caller.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode F)
    (hleaves : caller.stacks (persistent (mainExtraStacks c) 7) = []) :
    ∃ middle : Data c er,
    ∃ hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle),
    ∃ hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z (DyadicSchedule.M c.T n))
        (inputFrame c hr F middle),
    ∃ steps, steps ≤ bound c hr F (DyadicSchedule.M c.T n)
        (DyadicSchedule.M_ge_two c.T n) middle hf hb ∧
      Eval (procedure c hr).invoke steps caller
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) ∧
      Outcome c F (DyadicSchedule.M c.T n) caller
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb)
        (output c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) := by
  obtain ⟨middle, hf, hb, steps, ht, et, ho, _⟩ :=
    from_setup_detailed c hr F hF before caller hn hs hu hgood he hbody hleaves
  exact ⟨middle, hf, hb, steps, ht, et, ho⟩

/-- A fixed finite sequence executes the numerical setup and then the
normalization/worklist phase. The measured setup time is retained explicitly
so the independent setup runtime theorem can bound this same execution. -/
def withSetup (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    Procedure er (mainExtraStacks c) :=
  sequence (SubexpSetupProgram.mainProcedure c er) (procedure c hr)

theorem setup_invoke_detailed (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F) (before : Data c er)
    (hn : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 4)) =
      SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 5)) =
      SubexpPackingParameters.u n)
    (hgood : SubexpPackingParameters.GoodInput n)
    (hbody : before.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode F)
    (hleaves : before.stacks (persistent (mainExtraStacks c) 7) = []) :
    ∃ setupSteps, ∃ caller middle : Data c er,
    ∃ hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle),
    ∃ hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z (DyadicSchedule.M c.T n))
        (inputFrame c hr F middle),
    ∃ steps,
      Eval (SubexpSetupProgram.mainProcedure c er).invoke setupSteps before caller ∧
      steps ≤ setupSteps + bound c hr F (DyadicSchedule.M c.T n)
        (DyadicSchedule.M_ge_two c.T n) middle hf hb + 1 ∧
      Eval (withSetup c hr).invoke steps before
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) ∧
      Outcome c F (DyadicSchedule.M c.T n) caller
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb)
        (output c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) ∧
      NormalizationRun c F caller middle := by
  obtain ⟨ts, out, he, _, _, hp, _⟩ :=
    SubexpSetupProgram.main_execution c er n before hn hs hu
  have hcb := (hp 0 ⟨by decide, Or.inl (by decide)⟩).trans hbody
  have hcl := (hp 7 ⟨by decide, Or.inl (by decide)⟩).trans hleaves
  obtain ⟨middle, hf, hb, t, ht, et, ho, hnorm⟩ :=
    from_setup_detailed c hr F hF before _ hn hs hu hgood he hcb hcl
  exact ⟨ts, _, middle, hf, hb, ts + t + 1, he,
    Nat.add_le_add_right (Nat.add_le_add_left ht ts) 1,
    sequence_invoke _ _ he et, ho, hnorm⟩

theorem setup_invoke (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : ExecSparsifyObserved.Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost c.k F) (before : Data c er)
    (hn : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 4)) =
      SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat (before.stacks (persistent (mainExtraStacks c) 5)) =
      SubexpPackingParameters.u n)
    (hgood : SubexpPackingParameters.GoodInput n)
    (hbody : before.stacks (persistent (mainExtraStacks c) 0) = ExecSparsifyObserved.encode F)
    (hleaves : before.stacks (persistent (mainExtraStacks c) 7) = []) :
    ∃ setupSteps, ∃ caller middle : Data c er,
    ∃ hf : SubexpConcreteNode.FrameReady c (inputFrame c hr F middle),
    ∃ hb : SubexpConcreteNode.BankValues c (SparsificationConstants.z (DyadicSchedule.M c.T n))
        (inputFrame c hr F middle),
    ∃ steps,
      Eval (SubexpSetupProgram.mainProcedure c er).invoke setupSteps before caller ∧
      steps ≤ setupSteps + bound c hr F (DyadicSchedule.M c.T n)
        (DyadicSchedule.M_ge_two c.T n) middle hf hb + 1 ∧
      Eval (withSetup c hr).invoke steps before
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) ∧
      Outcome c F (DyadicSchedule.M c.T n) caller
        (result c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb)
        (output c hr F (DyadicSchedule.M c.T n) (DyadicSchedule.M_ge_two c.T n) middle hf hb) := by
  obtain ⟨ts, caller, middle, hf, hb, steps, es, ht, he, ho, _⟩ :=
    setup_invoke_detailed c hr F hF before hn hs hu hgood hbody hleaves
  exact ⟨ts, caller, middle, hf, hb, steps, es, ht, he, ho⟩

end SubexponentialSAT.SubexpOrderedRawSparsify

end OAI.Algorithms
