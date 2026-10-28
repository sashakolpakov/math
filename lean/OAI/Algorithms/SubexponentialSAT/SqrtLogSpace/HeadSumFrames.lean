import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackFrames

/-! Physical frames for the native head rescan. Read-and-restore source words
are framed at command endpoints. The pair accumulator has the stronger static
property that no controller, overlay or dense-add instruction writes it. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames

open OAI BitProgram StructuredCalls HeadSumProgram
open HeadEvaluationProgram.StagedGate (copy clear)
open CommandStackFrames

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

/-- Initial cleanup, copying and the first fuel test restore every retained
word outside the actual workspace and three initialized arrays. -/
theorem initial_frame (a : Data) (h : ℕ)
    (hshape : a.stacks 651 = List.replicate h false) (i : Fin 896)
    (hlow : 56 ≤ i.val) (hc : i ∉ HeadSumAssembly.controllerPorts)
    (hsum : i ≠ 853) :
    (CounterForPrograms.testResult fuelPorts
      (seeded (HeadSumAssembly.cleared a))).stacks i = a.stacks i := by
  have h859 : i ≠ 859 := by intro he; subst i; exact hc (by decide)
  have h860 : i ≠ 860 := by intro he; subst i; exact hc (by decide)
  have hc0 := HeadSumAssembly.cleared_controller a 859 (by decide)
  have hs0 := HeadSumAssembly.cleared_controller a 861 (by decide)
  have hshape' : (HeadSumAssembly.cleared a).stacks 651 = List.replicate h false :=
    (HeadSumAssembly.cleared_frame a 651 (by decide) (by decide)).trans hshape
  have hseed := seeded_stacks (HeadSumAssembly.cleared a) h hshape' hc0 hs0
  have hs : (seeded (HeadSumAssembly.cleared a)).stacks 861 = [] := by simp [hseed, hs0]
  rw [CounterForPrograms.testResult_stacks fuelPorts _ hs, hseed]
  simp only [Function.update_of_ne hsum, Function.update_of_ne h860,
    Function.update_of_ne h859]
  exact HeadSumAssembly.cleared_frame a i hlow hc

/-- The native cursor increment and fuel decrement change only their two
words and shared empty scratch; all semantic metadata survives this boundary. -/
theorem advance_frame (a : Data) (hs : a.stacks 861 = []) (i : Fin 896)
    (h859 : i ≠ 859) (h860 : i ≠ 860) (h861 : i ≠ 861) :
    (CounterForPrograms.nextState fuelPorts
      (Counters.incrementResult cursorPorts a)).stacks i = a.stacks i := by
  rw [← CounterForPrograms.nextState_outside fuelPorts
      (Counters.incrementResult cursorPorts a) i h860 h861,
    Counters.incrementResult_stacks cursorPorts a hs]
  exact Function.update_of_ne h859 _ _

/-- The final physical reclamation restores every off-controller word. -/
theorem final_frame {steps : ℕ} {a b : Data} (he : Eval finalize steps a b)
    (i : Fin 896) (h859 : i ≠ 859) (h860 : i ≠ 860) : b.stacks i = a.stacks i := by
  have hb := Eval.final_unique (853 : Fin 896) he (finalize_eval a)
  subst b
  simp [finalized_stacks, h859, h860]

/-- Full-key checks copy and temporarily consume their source words, then
restore all of them. This is an endpoint statement about the actual gate. -/
theorem gate_frame {steps : ℕ} {a b : Data}
    (rows : List (List (List Bool)))
    (hclean : ∀ i : Fin 32, a.stacks (HeadEvaluationProgram.StagedGate.stackMap i) = [])
    (hmatrix : a.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      (rows.map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hlen : ∀ row ∈ rows, row.length = (a.stacks 859).length)
    (hE : (a.stacks 859).length = (a.stacks 867).length)
    (hH : (a.stacks 859).length = (a.stacks 868).length)
    (he : Eval HeadEvaluationProgram.StagedGate.command steps a b) : b.stacks = a.stacks := by
  obtain ⟨_, _, out, hg, _⟩ := HeadEvaluationProgram.StagedGate.command_eval
    a rows hclean hmatrix hlen hE hH
  have hb : b = ⟨out, a.stacks⟩ := Eval.final_unique (853 : Fin 896) he hg
  rw [hb]

/-- The concrete overlay restores all source masks, baseline and query words
outside its precisely named assignment/output scratch. -/
theorem overlay_frame {steps : ℕ} {a b : Data}
    (hh : (a.stacks 859).length =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (he : Eval HighQueryAdapter.NativeOverlay.prepare steps a b)
    (i : Fin 896) (hi : i ∉ HighQueryAdapter.NativeOverlay.changed) :
    b.stacks i = a.stacks i := by
  open HighQueryAdapter.NativeOverlay in
    obtain ⟨rf, hc⟩ := command_eval (resetState a)
      (fun j hj => BankRoutines.clearBankStacks_mem j changed a.stacks hj)
      (by simpa only [reset_frame a 859 (by decide), reset_frame a 670 (by decide)] using hh)
      (by simpa only [reset_frame a 670 (by decide), reset_frame a 869 (by decide)] using hm)
    have hb := Eval.final_unique (853 : Fin 896) he ((reset_eval a).seq hc)
    subst b
    exact prepared_frame a rf i hi

private theorem bank_clear_writes (tmp : Fin 896) (ports : List (Fin 896))
    (i : Fin 896) (ht : i ≠ tmp) (hi : i ∉ ports) :
    i ∉ writes (BankRoutines.clearCmd tmp (0 : Fin 40) 1 ports) := by
  induction ports with
  | nil => exact not_mem_clearProgram _ _ _ _ ht
  | cons p ps ih =>
      have hp : i ≠ p := by intro he; subst i; exact hi (by simp)
      have hs : i ∉ ps := fun hm => hi (List.mem_cons_of_mem p hm)
      exact not_mem_union_iff.mpr ⟨not_mem_clearProgram _ _ _ _ hp, ih hs⟩

/-- No instruction in the actual overlay writes the pair accumulator. -/
theorem overlay_pair_not_mem : (851 : Fin 896) ∉ writes HighQueryAdapter.NativeOverlay.prepare := by
  apply not_mem_union_iff.mpr
  refine ⟨not_mem_union_iff.mpr ⟨not_mem_clearProgram _ _ _ _ (by decide),
    bank_clear_writes _ _ _ (by decide) (by decide)⟩, ?_⟩
  exact not_mem_liftProgram _ _ _ _ (by decide)

/-- Dense head addition and cache reset never write the pair accumulator.
The source and output arrays remain the actual854 and853. -/
theorem accumulate_pair_not_mem : (851 : Fin 896) ∉ writes accumulate := by
  apply not_mem_union_iff.mpr
  refine ⟨not_mem_liftProgram _ _ _ _ (by decide), ?_⟩
  apply not_mem_liftCommand_of
  intro j hj
  change j = 851 at hj
  subst j
  exact not_mem_clearMany FactorEnvironment.environmentPorts 851 (by decide)

/-- Static composition for the head controller. Its final concrete use supplies
the footprint of the named assignment program, rather than a semantic oracle. -/
theorem head_pair_not_mem (accepted : Code) (ha : (851 : Fin 896) ∉ writes accepted) :
    (851 : Fin 896) ∉ writes (HeadSumAssembly.head accepted) := by
  have hcopy (src dst : Fin 896) (hs : (851 : Fin 896) ≠ src) (hd : (851 : Fin 896) ≠ dst) :
      (851 : Fin 896) ∉ writes (copy src dst) :=
    not_mem_copyProgram _ _ _ _ _ _ hs hd (by decide)
  have hclear (src : Fin 896) (hs : (851 : Fin 896) ≠ src) :
      (851 : Fin 896) ∉ writes (clear src) := not_mem_clearProgram _ _ _ _ hs
  have hpower : (851 : Fin 896) ∉ writes power := not_mem_liftProgram _ _ _ _ (by decide)
  have hseed : (851 : Fin 896) ∉ writes seed := by
    exact not_mem_union_iff.mpr ⟨hcopy _ _ (by decide) (by decide),
      not_mem_union_iff.mpr ⟨hcopy _ _ (by decide) (by decide),
        not_mem_union_iff.mpr ⟨hpower, hclear _ (by decide)⟩⟩⟩
  have hstage : (851 : Fin 896) ∉ writes HeadEvaluationProgram.StagedGate.stage := by
    simp only [HeadEvaluationProgram.StagedGate.stage, writes, not_mem_union_iff]
    exact ⟨hcopy _ _ (by decide) (by decide), hcopy _ _ (by decide) (by decide),
      hcopy _ _ (by decide) (by decide), hcopy _ _ (by decide) (by decide),
      hcopy _ _ (by decide) (by decide), hcopy _ _ (by decide) (by decide)⟩
  have hcleanup : (851 : Fin 896) ∉ writes HeadEvaluationProgram.StagedGate.cleanup := by
    simp only [HeadEvaluationProgram.StagedGate.cleanup, writes, not_mem_union_iff]
    exact ⟨hclear _ (by decide), hclear _ (by decide), hclear _ (by decide),
      hclear _ (by decide), hclear _ (by decide), hclear _ (by decide)⟩
  have hgate : (851 : Fin 896) ∉ writes HeadEvaluationProgram.StagedGate.command :=
    not_mem_union_iff.mpr ⟨hstage, not_mem_union_iff.mpr
      ⟨not_mem_liftProgram _ _ _ _ (by decide), hcleanup⟩⟩
  have hinc : (851 : Fin 896) ∉ writes (Counters.incrementCmd cursorPorts) :=
    not_mem_liftProgram _ _ _ _ (by decide)
  have hbody : (851 : Fin 896) ∉ writes (body accepted) := by
    change (851 : Fin 896) ∉ writes HeadEvaluationProgram.StagedGate.command ∪
      ((writes accepted ∪ ∅) ∪ writes (Counters.incrementCmd cursorPorts))
    simp only [Finset.union_empty, not_mem_union_iff]
    exact ⟨hgate, ha, hinc⟩
  have hzero : (851 : Fin 896) ∉ writes (CounterForPrograms.zeroCmd fuelPorts) :=
    not_mem_liftProgram _ _ _ _ (by decide)
  have hdec : (851 : Fin 896) ∉ writes (CounterForPrograms.decrementCmd fuelPorts) :=
    not_mem_liftProgram _ _ _ _ (by decide)
  have htest : (851 : Fin 896) ∉ writes (CounterForPrograms.testCmd fuelPorts) := by
    change (851 : Fin 896) ∉ writes (CounterForPrograms.zeroCmd fuelPorts) ∪ ∅
    simpa only [Finset.union_empty] using hzero
  have hloop : (851 : Fin 896) ∉ writes (HeadSumProgram.command accepted) :=
    not_mem_union_iff.mpr ⟨htest, not_mem_union_iff.mpr ⟨hbody,
      not_mem_union_iff.mpr ⟨hdec, htest⟩⟩⟩
  have hfinal : (851 : Fin 896) ∉ writes finalize := by
    apply not_mem_liftCommand_of
    intro j hj
    change j = 851 at hj
    subst j
    exact not_mem_clearMany [859, 860] 851 (by decide)
  have hscan : (851 : Fin 896) ∉ writes (scan accepted) :=
    not_mem_union_iff.mpr ⟨hseed, not_mem_union_iff.mpr ⟨hloop, hfinal⟩⟩
  exact not_mem_union_iff.mpr ⟨not_mem_union_iff.mpr
    ⟨hclear _ (by decide), bank_clear_writes _ _ _ (by decide) (by
      rw [HeadSumAssembly.mem_workPorts]
      decide)⟩,
    not_mem_compiled _ _ _ _ hscan⟩

/-- The unchanged physical pair word transports any decoded meaning without
recomputing it, at every source prefix of the head command. -/
theorem head_pair_prefix (accepted : Code) (ha : (851 : Fin 896) ∉ writes accepted)
    {steps : ℕ} {a b : Cfg 40 896 (size (HeadSumAssembly.head accepted) + 1)}
    (ht : Trace (HeadSumAssembly.headProgram accepted) steps a b) :
    b.stacks 851 = a.stacks 851 :=
  compiled_trace_stack_frame _ _ _ ht 851 (head_pair_not_mem accepted ha)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumFrames
