import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBoundedSparsify
import OAI.Algorithms.SubexponentialSAT.SubexpMainNormalization

namespace OAI.Algorithms

/-!
# Physical normalization followed by sparsification

The first finite procedure normalizes the retained encoded formula. The second
resets the work registers, constructs the pending list, runs the actual finite
splitter, and transfers its leaves. The handoff uses the first procedure's
actual final state; no normalized input or empty work bank is assumed in its
place.
-/

namespace SubexponentialSAT.SubexpNormalizedSparsify

open BitProgram StructuredCalls SubexpMainProgram SubexpProcedureCompose

abbrev Formula := List (List ℕ)

def normalized (F : Formula) : Formula :=
  ExecCNF.normalize SubexpFrontend.negateCode F

abbrev formulaCode := SubexpNormalizationProgram.formulaCode

abbrev procedure {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels) : Procedure er es :=
  sequence (SubexpMainNormalization.procedure er es)
    (SubexpCanonicalSparsify.procedure splitter)

/-- The normalizer restores all five worklist slots. Its preservation of
persistent slot 7 supplies the initially empty leaf-stream port. -/
theorem handoff_ready {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (a : MainState er es) (ha : SubexpMainNormalization.WorkspaceClean a)
    (hleaves : a.stacks (persistent es 7) = []) :
    SubexpMainSparsify.Ready (SubexpMainSparsify.mainPorts er es)
      ((SubexpMainSparsify.procedure splitter).project a) := by
  constructor
  · intro i
    have h := ha (i.castAdd 12)
    change a.stacks ((SubexpMainSparsify.mainPorts er es).coreStack i) = []
    have hm : (SubexpMainSparsify.mainPorts er es).coreStack i =
        SubexpMainNormalization.workPort es (i.castAdd 12) := by
      apply Fin.ext
      change (SubexpMainSparsify.mainStack es (i.castAdd 2)).val = i.val
      rw [SubexpMainSparsify.mainStack_val]
      simp only [Fin.val_castAdd, i.isLt, ite_true]
    simpa only [hm] using h
  · change a.stacks ((SubexpMainSparsify.mainPorts er es).stack 6) = []
    simpa only [SubexpMainSparsify.mainPorts_output] using hleaves

theorem result_body {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool) :
    (SubexpCanonicalSparsify.result splitter caller body leaves).stacks
      (persistent es 0) = body := by
  let first := resetResult caller
  let p := SubexpMainSparsify.procedure splitter
  let out := SubexpMainSparsify.data (SubexpMainSparsify.mainPorts er es)
    (p.project first) (fun _ => false) [] [] body leaves
  have h := embedState_stack p.registerMap p.stack first out p.stack.injective
    (persistent es 0)
  change (SubexpCanonicalSparsify.result splitter caller body leaves).stacks
    (persistent es 0) = out.stacks (persistent es 0) at h
  refine h.trans ?_
  change (SubexpMainSparsify.data (SubexpMainSparsify.mainPorts er es)
    (p.project first) (fun _ => false) [] [] body leaves).stacks (persistent es 0) = body
  rw [← SubexpMainSparsify.mainPorts_source er es, SubexpMainSparsify.data_stack]
  rfl

/-- A storage invariant on an ordinary workspace prefix. The protected
runtime tables beyond this prefix may contain arbitrary data. -/
def EmptyPrefix {er es : ℕ} (count : ℕ) (a : MainState er es) : Prop :=
  ∀ i : Fin (totalStacks es), i.val < count → a.stacks i = []

theorem invoke_stack_frame {er es : ℕ} (p : Procedure er es)
    {n : ℕ} {a b : MainState er es} (h : Eval p.invoke n a b)
    (i : Fin (totalStacks es)) (hi : ¬ ∃ j, p.stack j = i) :
    b.stacks i = a.stacks i := by
  have hf := ProgramProjection.call_frame p.program p.registerMap p.stack
    p.registerMap_injective p.stack.injective h
  rw [hf]
  exact embedState_stack_frame p.registerMap p.stack a _ i hi

theorem normalization_high_frame {er es : ℕ} {n : ℕ} {a b : MainState er es}
    (h : Eval (SubexpMainNormalization.procedure er es).invoke n a b)
    (i : Fin (totalStacks es)) (hlo : 17 ≤ i.val) (hhi : i.val < workStacks es) :
    b.stacks i = a.stacks i := by
  apply invoke_stack_frame _ h i
  change ¬ ∃ j : Fin 18, SubexpMainNormalization.stackMap es j = i
  rintro ⟨j, hj⟩
  have hv := congrArg (fun x : Fin (totalStacks es) => x.val) hj
  change (SubexpMainNormalization.stackMap es j).val = i.val at hv
  by_cases h16 : j = 16
  · subst j
    change workStacks es = i.val at hv
    omega
  by_cases h17 : j = 17
  · subst j
    change 16 = i.val at hv
    omega
  · have hn16 : j.val ≠ 16 := fun he => h16 (Fin.ext he)
    have hn17 : j.val ≠ 17 := fun he => h17 (Fin.ext he)
    simp only [SubexpMainNormalization.stackMap, ite_eq_right h16, ite_eq_right h17] at hv
    have := j.isLt
    omega

theorem normalization_empty_prefix {er es : ℕ} {n : ℕ} {a b : MainState er es}
    (h : Eval (SubexpMainNormalization.procedure er es).invoke n a b)
    (hw : SubexpMainNormalization.WorkspaceClean b)
    (count : ℕ) (hcount : count ≤ workStacks es) (ha : EmptyPrefix count a) :
    EmptyPrefix count b := by
  intro i hi
  by_cases hlo : i.val < 17
  · let j : Fin 17 := ⟨i.val, hlo⟩
    have hm : SubexpMainNormalization.workPort es j = i := Fin.ext rfl
    simpa only [hm] using hw j
  · exact (normalization_high_frame h i (by omega) (by omega)).trans (ha i hi)

theorem result_work_register {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool) (i : Fin (workRegs er)) :
    (SubexpCanonicalSparsify.result splitter caller body leaves).regs
      (workRegister er i) = false := by
  let p := SubexpMainSparsify.procedure splitter
  let frame := p.project (resetResult caller)
  let out := SubexpMainSparsify.data (SubexpMainSparsify.mainPorts er es)
    frame (fun _ => false) [] [] body leaves
  have h := embedState_register p.registerMap p.stack (resetResult caller) out
    p.registerMap_injective i
  change (SubexpCanonicalSparsify.result splitter caller body leaves).regs
    (workRegister er i) = out.regs i at h
  refine h.trans ?_
  by_cases hi : ∃ j, (SubexpMainSparsify.mainPorts er es).register j = i
  · obtain ⟨j, rfl⟩ := hi
    exact SubexpMainSparsify.data_register _ _ _ _ _ _ _ j
  · exact (SubexpMainSparsify.data_register_frame _ _ _ _ _ _ _ i hi).trans
      (reset_work_register caller i)

private theorem io_core_empty (body leaves : List Bool) (i : Fin 5) :
    (WorklistIOProgram.ioState (fun _ => false) [] [] body leaves).stacks (i.castAdd 2) = [] := by
  fin_cases i <;> rfl

theorem result_empty_prefix {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool)
    (count : ℕ) (hcount : count ≤ workStacks es) (ha : EmptyPrefix count caller) :
    EmptyPrefix count (SubexpCanonicalSparsify.result splitter caller body leaves) := by
  intro i hi
  let p := SubexpMainSparsify.procedure splitter
  let ports := SubexpMainSparsify.mainPorts er es
  let frame := p.project (resetResult caller)
  let out := SubexpMainSparsify.data ports frame (fun _ => false) [] [] body leaves
  have h := embedState_stack p.registerMap p.stack (resetResult caller) out p.stack.injective i
  change (SubexpCanonicalSparsify.result splitter caller body leaves).stacks i = out.stacks i at h
  refine h.trans ?_
  by_cases hlo : i.val < 5
  · let j : Fin 5 := ⟨i.val, hlo⟩
    have hm : ports.stack (j.castAdd 2) = i := by
      apply Fin.ext
      change (SubexpMainSparsify.mainStack es (j.castAdd 2)).val = i.val
      rw [SubexpMainSparsify.mainStack_val]
      simp only [Fin.val_castAdd, j, hlo, ite_true]
    rw [← hm]
    exact (SubexpMainSparsify.data_stack _ _ _ _ _ _ _ _).trans (io_core_empty body leaves j)
  · have hn : ¬ ∃ j, ports.stack j = i := by
      rintro ⟨j, hj⟩
      have hv := congrArg (fun x : Fin (totalStacks es) => x.val) hj
      change (SubexpMainSparsify.mainStack es j).val = i.val at hv
      rw [SubexpMainSparsify.mainStack_val] at hv
      split_ifs at hv <;> omega
    have hf : out.stacks i = caller.stacks i := by
      have hd := SubexpMainSparsify.data_stack_frame ports frame (fun _ => false)
        [] [] body leaves i hn
      change out.stacks i = (resetResult caller).stacks i at hd
      rw [reset_stacks] at hd
      exact hd
    exact hf.trans (ha i hi)

def runtimeBound {er : ℕ} (F : Formula)
    (branch : ExecSparsifyWorklist.Branching Formula) (bound : ℕ) : ℕ :=
  3500 * ((formulaCode F).length + 1) ^ 2 +
    SubexpMainSparsify.runBound formulaCode branch bound (normalized F) + workRegs er + 3

/-- The splitter hypothesis is about the same finite table on the first
procedure's actual output. In particular it cannot replace normalization by
a semantic preprocessing operation. The resulting procedure has fixed control
independently of the formula and all runtime parameters stored with it. -/
theorem invoke {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (F : Formula) (caller : MainState er es)
    (hbody : caller.stacks (persistent es 0) = formulaCode F)
    (hwork : SubexpMainNormalization.WorkspaceClean caller)
    (hleaves : caller.stacks (persistent es 7) = [])
    (branch : ExecSparsifyWorklist.Branching Formula)
    (P : Formula → Prop) (cost : Formula → ℕ) (bound : ℕ)
    (hP : P (normalized F))
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ∀ (t : ℕ) (middle : MainState er es),
      Eval (SubexpMainNormalization.procedure er es).invoke t caller middle →
      ExecWorklistLoop.Ambient.BoundedRealizesOn splitter
        (SubexpMainSparsify.mainPorts er es).register
        (SubexpMainSparsify.mainPorts er es).coreStack
        (SubexpMainSparsify.workFrame (SubexpMainSparsify.mainPorts er es)
          ((SubexpMainSparsify.procedure splitter).project (resetResult middle))
          (formulaCode (normalized F)))
        formulaCode branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost formulaCode y (branch.split y) ≤ bound) :
    ∃ steps, steps ≤ runtimeBound (er := er) F branch bound ∧
      ∃ final : MainState er es, Eval (procedure splitter).invoke steps caller final ∧
        final.stacks (persistent es 0) = formulaCode (normalized F) ∧
        final.stacks (persistent es 7) = Encoding.encodeList formulaCode
          (ExecSparsifyWorklist.run branch
            (ExecSparsifyWorklist.initial (normalized F))).leaves ∧
        (∀ i : Fin 32, i ≠ 0 → i ≠ 7 →
          final.stacks (persistent es i) = caller.stacks (persistent es i)) ∧
        (∀ i : Fin 3, final.regs (controlRegister er i) = caller.regs (controlRegister er i)) ∧
        (∀ i : Fin (workRegs er), final.regs (workRegister er i) = false) ∧
        (∀ count, count ≤ workStacks es → EmptyPrefix count caller → EmptyPrefix count final) := by
  obtain ⟨tn, htn, middle, hn, hmw, hmb, hmp, hmc⟩ :=
    SubexpMainNormalization.invoke_eval F caller hbody hwork
  have hml : middle.stacks (persistent es 7) = [] :=
    (hmp 7 (by decide)).trans hleaves
  have hready := handoff_ready splitter middle hmw hml
  obtain ⟨ts, hts, hs⟩ := SubexpBoundedSparsify.canonical_invoke splitter middle hready
    formulaCode branch P cost bound (normalized F) hP hmb hclosed (hreal tn middle hn) hbound
  refine ⟨tn + ts + 1, ?_, _, sequence_invoke _ _ hn hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change tn ≤ 3500 * ((formulaCode F).length + 1) ^ 2 at htn
    dsimp [runtimeBound]
    omega
  · exact result_body splitter middle _ _
  · exact SubexpCanonicalSparsify.leaf_stream splitter middle _ _
  · intro i hi0 hi7
    exact (SubexpCanonicalSparsify.preserves_persistent splitter middle _ _ i hi0 hi7).trans
      (hmp i hi0)
  · intro i
    exact (SubexpCanonicalSparsify.preserves_control splitter middle _ _ i).trans (hmc i)
  · intro i
    exact result_work_register splitter middle _ _ i
  · intro count hcount ha
    exact result_empty_prefix splitter middle _ _ count hcount
      (normalization_empty_prefix hn hmw count hcount ha)

end SubexponentialSAT.SubexpNormalizedSparsify

end OAI.Algorithms
