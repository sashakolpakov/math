import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainBootPrefix
import OAI.Algorithms.SubexponentialSAT.SubexpActualSparsify
import OAI.Algorithms.SubexponentialSAT.SubexpMainReady

namespace OAI.Algorithms

/-!
# Actual raw-input boot of the SAT machine

The certificate records the same frontend, numerical setup, normalization and
observed-node worklist executions. It supplies no splitter, parameter words,
leaf list or cost oracle as input. The remaining sparsifier bound is explicitly
the bound of that concrete worklist, for the later runtime assembly.
-/

namespace SubexponentialSAT.SubexpMainBoot

open StructuredCalls SubexpMainProgram SubexpSetupProgram

abbrev Data (c : Config) (er : ℕ) := MainState er (mainExtraStacks c)

structure Run (c : Config) {er n : ℕ} (hr : 32 ≤ workRegs er)
    (F : SAT.CNF (Fin n)) where
  before : Data c er
  setupOutput : SetupState c
  middle : Data c er
  prefixSteps : ℕ
  setupSteps : ℕ
  sparsifySteps : ℕ
  frameReady : SubexpConcreteNode.FrameReady c (SubexpActualSparsify.inputFrame c hr F middle)
  bankValues : SubexpConcreteNode.BankValues c
    (SparsificationConstants.z (DyadicSchedule.M c.T n))
    (SubexpActualSparsify.inputFrame c hr F middle)
  prefixTrace : Eval (frontendProcedure er (mainExtraStacks c)).invoke prefixSteps
    (initialData er (mainExtraStacks c) (Encoding.encodeCNF F)) before
  setupTrace : Eval (mainProcedure c er).invoke setupSteps before
    ((mainProcedure c er).install before setupOutput)
  setupPost : SubexpSetupMainRuntime.Postconditions c er n before setupOutput
  sparsifyTrace : Eval (SubexpActualSparsify.procedure c hr).invoke sparsifySteps
    ((mainProcedure c er).install before setupOutput)
    (SubexpActualSparsify.result c hr F (DyadicSchedule.M c.T n)
      (DyadicSchedule.M_ge_two c.T n) middle frameReady bankValues)
  outcome : SubexpActualSparsify.Outcome c F (DyadicSchedule.M c.T n)
    ((mainProcedure c er).install before setupOutput)
    (SubexpActualSparsify.result c hr F (DyadicSchedule.M c.T n)
      (DyadicSchedule.M_ge_two c.T n) middle frameReady bankValues)
    (SubexpActualSparsify.output c hr F (DyadicSchedule.M c.T n)
      (DyadicSchedule.M_ge_two c.T n) middle frameReady bankValues)
  normalization : SubexpActualSparsify.NormalizationRun c F
    ((mainProcedure c er).install before setupOutput) middle
  sparsifyBound : sparsifySteps ≤ SubexpActualSparsify.bound c hr F (DyadicSchedule.M c.T n)
    (DyadicSchedule.M_ge_two c.T n) middle frameReady bankValues

namespace Run

variable {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er} {F : SAT.CNF (Fin n)}

noncomputable def afterSetup (run : Run c hr F) : Data c er :=
  (mainProcedure c er).install run.before run.setupOutput

noncomputable def afterSparsify (run : Run c hr F) : Data c er :=
  SubexpActualSparsify.result c hr F (DyadicSchedule.M c.T n)
    (DyadicSchedule.M_ge_two c.T n) run.middle run.frameReady run.bankValues

noncomputable def leaves (run : Run c hr F) : List (ExecSparsifyObserved.Formula n) :=
  SubexpActualSparsify.output c hr F (DyadicSchedule.M c.T n)
    (DyadicSchedule.M_ge_two c.T n) run.middle run.frameReady run.bankValues

noncomputable def records (run : Run c hr F) : List (List Bool) :=
  run.leaves.map ExecSparsifyObserved.encode

noncomputable def boot (run : Run c hr F) (p : Phases er (mainExtraStacks c))
    (hs : p.setup = mainProcedure c er) (ht : p.sparsify = SubexpActualSparsify.procedure c hr) :
    BootRun p run.before where
  afterSetup := run.afterSetup
  afterSparsify := run.afterSparsify
  setupSteps := run.setupSteps
  sparsifySteps := run.sparsifySteps
  setupTrace := by simpa only [hs, afterSetup] using run.setupTrace
  sparsifyTrace := by simpa only [ht, afterSetup, afterSparsify] using run.sparsifyTrace

theorem source (run : Run c hr F) :
    run.afterSparsify.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 7) =
      Encoding.encodeList id run.records := by
  rw [show Encoding.encodeList id run.records =
      Encoding.encodeList ExecSparsifyObserved.encode run.leaves from by
        simpa only [records, Function.comp_def, id_eq] using
          ExecSparsifyEncoding.encodeList_map ExecSparsifyObserved.encode id run.leaves]
  exact run.outcome.leaf_stream

theorem storageReady (run : Run c hr F) :
    SubexpMainReady.StorageReady (helperSize c) run.afterSparsify :=
  ⟨run.outcome.registers, run.outcome.workspace⟩

theorem setup_word (run : Run c hr F) (i : Fin 32) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    run.afterSparsify.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i) =
      run.setupOutput.stacks (SubexpSetupProgram.persistent c i) :=
  (run.outcome.persistent_frame i h0 h7).trans
    (main_install_word c er run.before run.setupOutput i)

theorem parameter_word_bound (run : Run c hr F) {B : ℕ}
    (hb : SubexpSetupStorage.WordBound B run.afterSetup)
    (i : Fin 32) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    (run.afterSparsify.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i)).length ≤ B := by
  exact (congrArg List.length (run.outcome.persistent_frame i h0 h7)).le.trans (hb _)

theorem persistent_empty (run : Run c hr F) (i : Fin 32)
    (hi : 8 ≤ i.val) (hi16 : i.val < 16) :
    run.afterSparsify.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i) = [] := by
  have h0 : i ≠ 0 := by intro h; subst i; change 8 ≤ 0 at hi; omega
  have h6 : i ≠ 6 := by intro h; subst i; change 8 ≤ 6 at hi; omega
  have h7 : i ≠ 7 := by intro h; subst i; change 8 ≤ 7 at hi; omega
  have hp := SubexpMainBootPrefix.facts_of_execution F run.prefixTrace
  exact (run.outcome.persistent_frame i h0 h7).trans
    ((run.setupPost.retained i ⟨h6, Or.inl hi16⟩).trans (hp.empty i (by omega)))

theorem satisfiable (run : Run c hr F) :
    SAT.Satisfiable F ↔ ∃ G ∈ run.leaves, SAT.Satisfiable (ExecCNF.formulaSet G) :=
  run.outcome.satisfiable

end Run

/-- For fixed clause width and storage, the actual boot exists on every
sufficiently large input. The setup costs and stored words have one fixed
polynomial bound; the concrete sparsification cost remains in `Run`. -/
theorem eventually_run (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ F : SAT.CNF (Fin n), SAT.WidthAtMost c.k F →
        ∃ run : Run c hr F,
          run.prefixSteps + run.setupSteps ≤ C * (Encoding.formulaBitLength F + 1) ^ d ∧
          SubexpSetupStorage.WordBound (C * (Encoding.formulaBitLength F + 1) ^ d)
            run.afterSetup := by
  obtain ⟨C, d, hC, hd, hb⟩ := SubexpSetupMainRuntime.eventually_raw_bounded c er
  refine ⟨C, d, hC, hd, ?_⟩
  filter_upwards [hb, SubexpPackingParameters.eventually_goodInput] with n hb hgood
  intro F hF
  obtain ⟨tp, ts, before, out, _, hp, hs, hcost, hwords, hpost⟩ := hb F
  have hf := SubexpMainBootPrefix.facts_of_execution F hp
  have hbody := (hpost.retained 0 ⟨by decide, Or.inl (by decide)⟩).trans hf.body
  have hleaves := (hpost.retained 7 ⟨by decide, Or.inl (by decide)⟩).trans (hf.empty 7 (by decide))
  obtain ⟨middle, hframe, hbank, tt, htime, ht, hresult, hnorm⟩ :=
    SubexpActualSparsify.from_setup_detailed c hr F hF before _
      hf.variableCount hf.scale hf.capacity hgood hs hbody hleaves
  let run : Run c hr F :=
    { before := before, setupOutput := out, middle := middle
      prefixSteps := tp, setupSteps := ts, sparsifySteps := tt
      frameReady := hframe, bankValues := hbank
      prefixTrace := hp, setupTrace := hs, setupPost := hpost
      sparsifyTrace := ht, outcome := hresult, normalization := hnorm, sparsifyBound := htime }
  exact ⟨run, hcost, hwords⟩

end SubexponentialSAT.SubexpMainBoot

end OAI.Algorithms
