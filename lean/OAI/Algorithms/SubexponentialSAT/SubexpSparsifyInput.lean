import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupMainExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizedSparsify
import OAI.Algorithms.SubexponentialSAT.SubexpConcreteNode
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram

namespace OAI.Algorithms

/-!
# The actual setup-to-sparsifier input

The numerical setup computes the threshold bank, the normalizer preserves it,
and the register reset supplies the canonical node frame.  The statements
below concern those actual executions.  In particular, no independently
assumed certificate replaces the setup or normalization program.

The raw length bound is inherited from the table producer, including padded
binary input words.  Only the low search workspace enters the node's initial
active-bit count; unrelated preserved caller words need no size hypothesis.
-/

namespace SubexponentialSAT.SubexpSparsifyInput

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage
open SubexpMainProgram (MainState workRegs workStacks totalStacks)
open SubexpProcedureCompose (resetResult)

/-- A postcondition of the actual table producer, relative to its retained M
word.  This is an assertion on raw lists, not on canonical binary encodings. -/
def ThresholdWidths (c : Config) (a : SetupState c) : Prop :=
  ∀ i : Fin (thresholdCount c),
    (a.stacks (threshold c i)).length ≤
      ArithmeticExpressionProgram.widthCoeff
        (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
          ((a.stacks (persistent c 23)).length + 1)

theorem thresholdWidths_frame (c : Config) {a b : SetupState c}
    (h : ThresholdWidths c a)
    (hf : ∀ i, Protected c i → b.stacks i = a.stacks i) :
    ThresholdWidths c b := by
  intro i
  rw [hf _ (threshold_protected c i), hf _ (persistent_protected c 23)]
  exact h i

/-- Recover the producer's length postcondition without changing the frozen
numerical setup correctness interface. -/
theorem scalarSetup_table_witness (c : Config) (n : ℕ) (a : SetupState c)
    (hgood : SubexpPackingParameters.GoodInput n)
    (hk : Known c n initialKnown a) :
    ∃ t b, Eval (scalarSetup c) t a b ∧ ThresholdWidths c b ∧
      b.stacks (persistent c 23) =
        SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨tn, an, en, kn, _⟩ := numericSetup_eval c n a hgood hk
  have mn := numericSetup_Mword c n hgood hk en
  obtain ⟨tt, rf, words, _, et, vt, _, _⟩ := SubexpSetupPhaseTable.table_eval c an
  let atab := SubexpSetupPhaseTable.tableResult c an rf words
  have ft : ∀ i : Fin 32, atab.stacks (persistent c i) = an.stacks (persistent c i) :=
    SubexpSetupPhaseTable.table_result_persistent c an rf words
  have kt := known_frame c n finalKnown an atab kn ft
  have wt : ThresholdWidths c atab := by
    intro i
    rw [ft 23]
    exact (vt i).2
  obtain ⟨tg, b, eg, _, fg⟩ := readyGuard_eval c n atab
    (kt 4 (by simp [finalKnown])) (kt 28 (by simp [finalKnown]))
    (kt 19 (by simp [finalKnown])) (kt 20 (by simp [finalKnown]))
    (kt 26 (by simp [finalKnown])) (kt 27 (by simp [finalKnown]))
  have eall := Eval.seq en (Eval.seq et eg)
  exact ⟨_, b, eall, thresholdWidths_frame c wt fg,
    (fg _ (persistent_protected c 23)).trans ((ft 23).trans mn)⟩

theorem command_table_witness (c : Config) (n : ℕ) (a : SetupState c)
    (hgood : SubexpPackingParameters.GoodInput n)
    (hk : Known c n initialKnown a) :
    ∃ t b, Eval (command c) t a b ∧ ThresholdWidths c b ∧
      b.stacks (persistent c 23) =
        SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨te, ae, ee, ve, fe⟩ := early_eval c a
  have ke := known_frame c n initialKnown a ae hk
    (fun i => fe _ (persistent_protected c i))
  have hpass : ae.regs 15 = true := ve.mpr (by
    rw [show BinaryArithmetic.toNat (a.stacks (persistent c 4)) =
      SubexpPackingParameters.s n from hk 4 (by decide)]
    exact hgood)
  obtain ⟨ts, bs, es, ws, ms⟩ := scalarSetup_table_witness c n ae hgood ke
  obtain ⟨ec, fc, _⟩ := workspace_cleanup c bs
  have eall : Eval (command c) ((te + (ts + 1)) + clearManyCost (workspacePorts c) bs)
      a (clearManyState (workspacePorts c) bs) := .seq (.seq ee (.ite_true hpass es)) ec
  exact ⟨_, _, eall,
    thresholdWidths_frame c ws (fun i hi => fc.2 i hi (by simp)),
    (fc.2 _ (persistent_protected c 23) (by simp)).trans ms⟩

/-- Every execution of the closed command has the same producer bound. -/
theorem command_thresholdWidths (c : Config) (n : ℕ)
    {a b : SetupState c} {t : ℕ}
    (hgood : SubexpPackingParameters.GoodInput n)
    (hk : Known c n initialKnown a) (he : Eval (command c) t a b) :
    ThresholdWidths c b := by
  obtain ⟨tw, bw, ew, hw, _⟩ := command_table_witness c n a hgood hk
  have hb := SubexpPrimeProgram.eval_result_unique he ew (persistent c 0) (persistent c 0)
  simpa only [hb] using hw

theorem command_Mword (c : Config) (n : ℕ)
    {a b : SetupState c} {t : ℕ}
    (hgood : SubexpPackingParameters.GoodInput n)
    (hk : Known c n initialKnown a) (he : Eval (command c) t a b) :
    b.stacks (persistent c 23) =
      SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨tw, bw, ew, _, hm⟩ := command_table_witness c n a hgood hk
  have hb := SubexpPrimeProgram.eval_result_unique he ew (persistent c 0) (persistent c 0)
  simpa only [hb] using hm

def MainThresholdWidths (c : Config) {er : ℕ}
    (a : MainState er (mainExtraStacks c)) : Prop :=
  ∀ i : Fin (thresholdCount c),
    (a.stacks (mainStack c (threshold c i))).length ≤
      ArithmeticExpressionProgram.widthCoeff
        (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
          ((a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23)).length + 1)

theorem initialKnown_project (c : Config) {er n : ℕ}
    (a : MainState er (mainExtraStacks c))
    (hn : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 4)) =
        SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 5)) =
        SubexpPackingParameters.u n) :
    Known c n initialKnown ((mainProcedure c er).project a) := by
  apply initialKnown_of_words c n _
  · rw [main_project_word]; exact hn
  · rw [main_project_word]; exact hs
  · rw [main_project_word]; exact hu

/-- The real procedure call has the same raw threshold-length bounds as its
local command.  Determinism connects the witnessed run to the caller's run. -/
theorem main_table_post (c : Config) {er n t : ℕ}
    {a b : MainState er (mainExtraStacks c)}
    (hgood : SubexpPackingParameters.GoodInput n)
    (hk : Known c n initialKnown ((mainProcedure c er).project a))
    (he : Eval (mainProcedure c er).invoke t a b) :
    MainThresholdWidths c b ∧
      b.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) =
        SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨tw, out, ew, hw, hm⟩ := command_table_witness c n
    ((mainProcedure c er).project a) hgood hk
  have et := (mainProcedure c er).invoke_trace a out
    (compiled_halt_trace ew (persistent c 0) (persistent c 0))
  have hb := SubexpPrimeProgram.eval_result_unique he et
    (SubexpMainProgram.persistent (mainExtraStacks c) 0)
    (SubexpMainProgram.persistent (mainExtraStacks c) 0)
  constructor
  · intro i
    rw [hb, main_install_word]
    have ht := embedState_stack (mainProcedure c er).registerMap (mainProcedure c er).stack
      a out (mainProcedure c er).stack.injective (threshold c i)
    change ((mainProcedure c er).install a out).stacks (mainStack c (threshold c i)) =
      out.stacks (threshold c i) at ht
    rw [ht]
    exact hw i
  · rw [hb, main_install_word c er a out (23 : Fin 32)]
    exact hm

theorem main_thresholdWidths (c : Config) {er n t : ℕ}
    {a b : MainState er (mainExtraStacks c)}
    (hgood : SubexpPackingParameters.GoodInput n)
    (hk : Known c n initialKnown ((mainProcedure c er).project a))
    (he : Eval (mainProcedure c er).invoke t a b) : MainThresholdWidths c b :=
  (main_table_post c hgood hk he).1

/-- Concrete postconditions of any actual setup call from the frontend's
three numeric words.  No cleared-workspace or threshold premise is required. -/
theorem setup_post (c : Config) {er n t : ℕ}
    {a b : MainState er (mainExtraStacks c)}
    (hn : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 4)) =
        SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 5)) =
        SubexpPackingParameters.u n)
    (hgood : SubexpPackingParameters.GoodInput n)
    (he : Eval (mainProcedure c er).invoke t a b) :
    SubexpNormalizedSparsify.EmptyPrefix (helperSize c) b ∧
    BinaryArithmetic.toNat
      (b.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23)) =
        DyadicSchedule.M c.T n ∧
    (∀ i : Fin (thresholdCount c),
      BinaryArithmetic.toNat (b.stacks (mainStack c (threshold c i))) =
        SparsificationConstants.z (DyadicSchedule.M c.T n) (i.val + 2)) ∧
    MainThresholdWidths c b ∧
    b.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) =
      SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨tw, out, ew, _, hv, _, hw⟩ := main_execution c er n a hn hs hu
  have hb := SubexpPrimeProgram.eval_result_unique he ew
    (SubexpMainProgram.persistent (mainExtraStacks c) 0)
    (SubexpMainProgram.persistent (mainExtraStacks c) 0)
  refine ⟨?_, ?_, ?_, main_table_post c hgood (initialKnown_project c a hn hs hu) he⟩
  · intro i hi
    let j : Fin (stackCount c) := Fin.cast (main_stackCount c).symm i
    have hj : mainStack c j = i := Fin.ext rfl
    rw [hb, ← hj]
    exact hw j hi
  · rw [hb, main_install_word c er a out (23 : Fin 32)]
    exact (hv hgood).1.M
  · intro i
    rw [hb]
    exact (congrArg BinaryArithmetic.toNat
      (embedState_stack (mainProcedure c er).registerMap (mainProcedure c er).stack
        a out (mainProcedure c er).stack.injective (threshold c i))).trans ((hv hgood).2 i)

/-- The exact worklist frame used after the physical register reset. -/
noncomputable abbrev inputFrame (c : Config) {er labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    (middle : MainState er (mainExtraStacks c)) (body : List Bool) :
    SubexpConcreteNode.Frame c er :=
  SubexpMainSparsify.workFrame (SubexpMainSparsify.mainPorts er (mainExtraStacks c))
    ((SubexpMainSparsify.procedure splitter).project (resetResult middle)) body

theorem inputFrame_registers (c : Config) {er labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    (middle : MainState er (mainExtraStacks c)) (body : List Bool) :
    ∀ i, (inputFrame c splitter middle body).regs i = false := by
  intro i
  let ports := SubexpMainSparsify.mainPorts er (mainExtraStacks c)
  by_cases hi : ∃ j, ports.register j = i
  · obtain ⟨j, rfl⟩ := hi
    exact SubexpMainSparsify.data_register _ _ _ _ _ _ _ j
  · exact (SubexpMainSparsify.data_register_frame _ _ _ _ _ _ _ i hi).trans
      (SubexpProcedureCompose.reset_work_register middle i)

theorem inputFrame_work_stack (c : Config) {er labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    (middle : MainState er (mainExtraStacks c)) (body : List Bool)
    (i : Fin (totalStacks (mainExtraStacks c)))
    (hlo : 5 ≤ i.val) (hhi : i.val < workStacks (mainExtraStacks c)) :
    (inputFrame c splitter middle body).stacks i = middle.stacks i := by
  have hn : ¬ ∃ j, (SubexpMainSparsify.mainPorts er (mainExtraStacks c)).stack j = i := by
    rintro ⟨j, hj⟩
    have hv := congrArg (fun x : Fin (totalStacks (mainExtraStacks c)) => x.val) hj
    change (SubexpMainSparsify.mainStack (mainExtraStacks c) j).val = i.val at hv
    rw [SubexpMainSparsify.mainStack_val] at hv
    split_ifs at hv <;> omega
  have hf := SubexpMainSparsify.data_stack_frame
    (SubexpMainSparsify.mainPorts er (mainExtraStacks c))
    ((SubexpMainSparsify.procedure splitter).project (resetResult middle))
    (fun _ => false) [] [] body [] i hn
  change (inputFrame c splitter middle body).stacks i = (resetResult middle).stacks i at hf
  rw [SubexpProcedureCompose.reset_stacks] at hf
  exact hf

theorem inputFrame_M (c : Config) {er labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    (middle : MainState er (mainExtraStacks c)) (body : List Bool) :
    (inputFrame c splitter middle body).stacks
      (SubexpMainProgram.persistent (mainExtraStacks c) 23) =
        middle.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) := by
  have hf := SubexpMainSparsify.main_data_preserves_persistent er (mainExtraStacks c)
    ((SubexpMainSparsify.procedure splitter).project (resetResult middle))
    (fun _ => false) [] [] body [] 23 (by decide) (by decide)
  change (inputFrame c splitter middle body).stacks
      (SubexpMainProgram.persistent (mainExtraStacks c) 23) =
    (resetResult middle).stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) at hf
  rw [SubexpProcedureCompose.reset_stacks] at hf
  exact hf

theorem threshold_low (c : Config) (i : Fin (thresholdCount c)) :
    17 ≤ (mainStack c (threshold c i)).val := by
  change 17 ≤ helperSize c + i.val
  have := helperSize_ge c
  omega

theorem threshold_high (c : Config) (i : Fin (thresholdCount c)) :
    (mainStack c (threshold c i)).val < workStacks (mainExtraStacks c) := by
  change helperSize c + i.val < workStacks (mainExtraStacks c)
  have hi := i.isLt
  have hf := SubexpNodePorts.setup_fit c
  change i.val < c.k - 1 at hi
  omega

theorem inputFrame_threshold (c : Config) {er labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    (middle : MainState er (mainExtraStacks c)) (body : List Bool)
    (i : Fin (thresholdCount c)) :
    (inputFrame c splitter middle body).stacks (mainStack c (threshold c i)) =
      middle.stacks (mainStack c (threshold c i)) :=
  inputFrame_work_stack c splitter middle body _
    (by have := threshold_low c i; omega) (threshold_high c i)

theorem inputFrame_ready (c : Config) {er labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    (middle : MainState er (mainExtraStacks c)) (body : List Bool)
    (hw : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) middle) :
    SubexpConcreteNode.FrameReady c (inputFrame c splitter middle body) := by
  refine ⟨inputFrame_registers c splitter middle body, ?_⟩
  intro i hlo hhi
  rw [inputFrame_work_stack c splitter middle body i hlo
    (by have := mainWorkStacks_ge c; omega)]
  exact hw i (by have := helperSize_ge c; omega)

/-- The real normalizer preserves all threshold words and M while restoring
the ordinary prefix. Its output workspace is obtained from its proved run. -/
theorem normalization_post (c : Config) {er t : ℕ}
    {a b : MainState er (mainExtraStacks c)} (F : List (List ℕ))
    (hbody : a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 0) =
      SubexpNormalizationProgram.formulaCode F)
    (ha : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) a)
    (he : Eval (SubexpMainNormalization.procedure er (mainExtraStacks c)).invoke t a b) :
    SubexpNormalizedSparsify.EmptyPrefix (helperSize c) b ∧
    (∀ i : Fin (thresholdCount c), b.stacks (mainStack c (threshold c i)) =
      a.stacks (mainStack c (threshold c i))) ∧
    b.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) =
      a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) := by
  have hwa : SubexpMainNormalization.WorkspaceClean a := by
    intro i
    apply ha
    change i.val < helperSize c
    have := i.isLt
    have := helperSize_ge c
    omega
  obtain ⟨tw, _, bw, ew, hww, _, hp, _⟩ :=
    SubexpMainNormalization.invoke_eval F a hbody hwa
  have hb := SubexpPrimeProgram.eval_result_unique he ew
    (SubexpMainProgram.persistent (mainExtraStacks c) 0)
    (SubexpMainProgram.persistent (mainExtraStacks c) 0)
  have hwb : SubexpMainNormalization.WorkspaceClean b := by
    rw [hb]
    exact hww
  refine ⟨SubexpNormalizedSparsify.normalization_empty_prefix he hwb (helperSize c)
    (by have := SubexpNodePorts.setup_fit c; omega) ha, ?_, ?_⟩
  · intro i
    exact SubexpNormalizedSparsify.normalization_high_frame he _
      (threshold_low c i) (threshold_high c i)
  · rw [hb]
    exact hp 23 (by decide)

/-- The complete input join. The only state premises are actual setup and
normalization executions, the frontend's numeric words, and its encoded body.
The resulting frame is exactly the one consumed by the worklist's node call. -/
theorem setup_normalization_input (c : Config) {er n labels ts tn : ℕ}
    (hr : 32 ≤ workRegs er)
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    {a caller middle : MainState er (mainExtraStacks c)}
    (hn : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 2)) = n)
    (hs : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 4)) =
        SubexpPackingParameters.s n)
    (hu : BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 5)) =
        SubexpPackingParameters.u n)
    (hgood : SubexpPackingParameters.GoodInput n)
    (es : Eval (mainProcedure c er).invoke ts a caller)
    (F : List (List ℕ))
    (hbody : caller.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 0) =
      SubexpNormalizationProgram.formulaCode F)
    (en : Eval (SubexpMainNormalization.procedure er (mainExtraStacks c)).invoke tn caller middle)
    (body : List Bool) :
    let frame := SubexpConcreteNode.localFrame c hr (inputFrame c splitter middle body)
    ExecSparsifyBoundary.FrameReady frame ∧
    ExecSparsifyObserved.BankValues (SparsificationConstants.z (DyadicSchedule.M c.T n)) frame ∧
    BinaryArithmetic.toNat (frame.stacks (SubexpNodePorts.mPort c.k)) = DyadicSchedule.M c.T n ∧
    (∀ i : Fin (thresholdCount c),
      (frame.stacks (SubexpNodePorts.thresholdPort c.k i)).length ≤
        ArithmeticExpressionProgram.widthCoeff
          (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
            ((frame.stacks (SubexpNodePorts.mPort c.k)).length + 1)) ∧
    frame.stacks (SubexpNodePorts.mPort c.k) =
      SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨hw, hm, hv, hwidth, hword⟩ := setup_post c hn hs hu hgood es
  obtain ⟨hmw, hmt, hmm⟩ := normalization_post c F hbody hw en
  have hft (i : Fin (thresholdCount c)) :
      (inputFrame c splitter middle body).stacks (mainStack c (threshold c i)) =
        caller.stacks (mainStack c (threshold c i)) :=
    (inputFrame_threshold c splitter middle body i).trans (hmt i)
  have hfm : (inputFrame c splitter middle body).stacks
      (SubexpMainProgram.persistent (mainExtraStacks c) 23) =
        caller.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) :=
    (inputFrame_M c splitter middle body).trans hmm
  have hlocalM : (SubexpConcreteNode.localFrame c hr (inputFrame c splitter middle body)).stacks
      (SubexpNodePorts.mPort c.k) =
        caller.stacks (SubexpMainProgram.persistent (mainExtraStacks c) 23) := by
    change (inputFrame c splitter middle body).stacks
      (SubexpNodePorts.setupStackMap c (SubexpNodePorts.mPort c.k)) = _
    rw [SubexpNodePorts.setupStackMap_M]
    exact hfm
  have hlocalT (i : Fin (thresholdCount c)) :
      (SubexpConcreteNode.localFrame c hr (inputFrame c splitter middle body)).stacks
        (SubexpNodePorts.thresholdPort c.k i) = caller.stacks (mainStack c (threshold c i)) :=
    (SubexpNodeRealization.setup_project_threshold c hr _ i).trans (hft i)
  dsimp only
  refine ⟨SubexpConcreteNode.local_ready c hr _ (inputFrame_ready c splitter middle body hmw),
    SubexpConcreteNode.local_bank c hr _ _ ?_, ?_, ?_, hlocalM.trans hword⟩
  · intro i
    rw [hft i]
    exact hv i
  · rw [hlocalM]
    exact hm
  · intro i
    rw [hlocalT i, hlocalM]
    exact hwidth i

/-- The low search workspace contains exactly the current formula. The
protected numerical bank and caller caches do not enter this count. -/
theorem input_localSearchBits (c : Config) {er n labels : ℕ}
    (hr : 32 ≤ workRegs er)
    (splitter : Program (workRegs er) (totalStacks (mainExtraStacks c)) labels)
    (middle : MainState er (mainExtraStacks c)) (body : List Bool)
    (hw : SubexpNormalizedSparsify.EmptyPrefix (helperSize c) middle)
    (F : ExecSparsifyObserved.Formula n) :
    ExecSparsifySearchFrame.localSearchBits
      (ExecSparsifyObserved.localInput
        (SubexpConcreteNode.localFrame c hr (inputFrame c splitter middle body)) F) =
      (ExecSparsifyObserved.encode F).length := by
  exact ExecSparsifyExecution.localInput_bits
    (SubexpConcreteNode.local_ready c hr _ (inputFrame_ready c splitter middle body hw))

/-- Copying the current head formula into the search workspace leaves each
actual threshold word unchanged, so the producer bound prices later copies. -/
theorem localInput_threshold_word {n k : ℕ} (frame : ExecSparsifyNode.Data k)
    (F : ExecSparsifyObserved.Formula n) (i : ExecCNFWidthDriver.Width k) :
    (ExecSparsifyObserved.localInput frame F).stacks
      (ExecCNFWidthLoad.bank k (ExecCNFWidthDriver.dimension i)
        (ExecCNFWidthDriver.dimension_le i)) =
      frame.stacks (SubexpNodePorts.thresholdPort k i) := by
  have hne : ExecSparsifyProgram.searchPort k
      (ExecCNFWidthLoad.bank k (ExecCNFWidthDriver.dimension i)
        (ExecCNFWidthDriver.dimension_le i)) ≠ ExecSparsifyNode.port k 21 := by
    intro h
    have hv := congrArg Fin.val h
    change 5 + (33 + ExecCNFWidthDriver.dimension i) = 21 at hv
    omega
  change (ExecSparsifyNode.headLoaded (ExecSparsifyObserved.encode F)
      (ExecSparsifyCanonicalHead.input ExecSparsifyObserved.encode frame F [] [] 0)).stacks
    (ExecSparsifyProgram.searchPort k (ExecCNFWidthLoad.bank k
      (ExecCNFWidthDriver.dimension i) (ExecCNFWidthDriver.dimension_le i))) = _
  rw [ExecSparsifyNode.headLoaded_stack_frame _ _ _ hne,
    ExecSparsifyCanonicalHead.input_search_stack, SubexpConcreteNode.search_threshold_eq]

end SubexponentialSAT.SubexpSparsifyInput

end OAI.Algorithms
