import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticSelectorAdapter
import OAI.Algorithms.SubexponentialSAT.SubexpMainFieldCache
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose

namespace OAI.Algorithms

/-!
# Actual selection, prepared rings, nodes, and field caches in Main

Only the prime, precision and exponent are supplied as semantic inputs.
Every later phase consumes the preceding phase's actual result.  Old selected,
prepared-ring and node-table contents are allowed, and their erasure remains
in the measured bounds.  Field output slots and the save slot start empty.
-/

namespace SubexponentialSAT.SubexpMainCacheSetup

open BitProgram StructuredCalls SubexpMainProgram
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open SubexpLayoutPorts (ordinary master)

abbrev Allocation := SubexpLayoutPorts.Allocation

def cacheAllocation {es : ℕ} (alloc : Allocation es) : SubexpMainFieldCache.Allocation es where
  ordinaryCount := alloc.ordinaryCount
  enough := by have := alloc.enough; omega
  within := alloc.within

def nodeAllocation {es : ℕ} (alloc : Allocation es) : SubexpMainFieldNodes.Allocation es :=
  SubexpMainFieldCache.nodeAllocation (cacheAllocation alloc)

def ringAllocation {es : ℕ} (alloc : Allocation es) : SubexpMainPreparedRings.Allocation es :=
  SubexpMainFieldCache.ringAllocation (cacheAllocation alloc)

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpQuarticSelectorAdapter.procedure er es)
    (SubexpProcedureCompose.sequence (SubexpMainPreparedRings.procedure er (ringAllocation alloc))
      (SubexpProcedureCompose.sequence (SubexpMainFieldNodes.procedure er (nodeAllocation alloc))
        (SubexpMainFieldCache.procedure er (cacheAllocation alloc))))

def program (er : ℕ) {es : ℕ} (alloc : Allocation es) :=
  ProgramLinking.liftProgram (procedure er alloc).program
    (procedure er alloc).registerMap (procedure er alloc).stack

def initiallyEmpty (i : Fin 672) : Prop :=
  i.val < 110 ∨ (135 ≤ i.val ∧ i.val ≤ 137) ∨ i.val = 300

def WorkspaceReady {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : Prop :=
  ∀ i, initiallyEmpty i → a.stacks (ordinary alloc i) = []

def changedPersistent : List (Fin 32) := [12, 13, 14, 15, 28, 30, 31]

theorem ordinary_ne_persistent {es : ℕ} (alloc : Allocation es) (i : Fin 672) (j : Fin 32) :
    ordinary alloc i ≠ persistent es j := by
  intro h
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
  have hw := alloc.enough.trans alloc.within
  change i.val = workStacks es + j.val at hv
  omega

theorem work_ne_persistent {es : ℕ} (i : Fin (totalStacks es))
    (hi : i.val < workStacks es) (j : Fin 32) : i ≠ persistent es j := by
  intro h
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
  change i.val = workStacks es + j.val at hv
  omega

theorem selector_ready {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (ha : WorkspaceReady alloc a) : SubexpQuarticSelectorAdapter.WorkspaceReady a := by
  intro i
  exact ha ⟨i.val, by omega⟩ (Or.inl (by change i.val < 110; have := i.isLt; omega))

theorem selector_persistent_frame {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : SubexpQuarticSelectorAdapter.WorkspaceReady a) (i : Fin 32) (hi : i ≠ 15) :
    (SubexpQuarticSelectorAdapter.result a p).stacks (persistent es i) =
      a.stacks (persistent es i) := by
  rw [SubexpQuarticSelectorAdapter.result_stacks a p ha,
    Function.update_of_ne (fun h => hi ((persistent_injective es) h))]

theorem selector_workspace {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p : ℕ) [Fact p.Prime] (ha : WorkspaceReady alloc a) :
    WorkspaceReady alloc (SubexpQuarticSelectorAdapter.result a p) := by
  intro i hi
  rw [SubexpQuarticSelectorAdapter.result_stacks a p (selector_ready alloc a ha),
    Function.update_of_ne (ordinary_ne_persistent alloc i 15)]
  exact ha i hi

/-- The three witnesses are results of the actual selected-coefficient,
prepared-ring, node and cache executions, rather than supplied dictionaries. -/
structure Result {er es : ℕ} (alloc : Allocation es) (a e : MainState er es)
    (p D : ℕ) [Fact p.Prime] : Prop where
  stages : ∃ b c,
    SubexpMainPreparedRings.SelectedResult (ringAllocation alloc)
      (SubexpQuarticSelectorAdapter.result a p) b p D ∧
    SubexpMainFieldNodes.Result (nodeAllocation alloc) b c p (D + 1)
      (SubexpPreparedQuarticSetup.modulus p 1) ∧
    SubexpMainFieldCache.Result (cacheAllocation alloc) c e p D
  selected : e.stacks (persistent es 15) = SubexpQuarticSelectorAdapter.selectedBytes p
  target : ∀ i, e.stacks (persistent es (SubexpMainPreparedRings.targetIndex i)) =
    SubexpPreparedRingStaging.bankWords p D
      (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
      (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) i
  source : ∀ i, e.stacks (SubexpMainPreparedRings.sourcePort (ringAllocation alloc) i) =
    SubexpPreparedRingStaging.bankWords p 0
      (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
      (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) i
  lifted : e.stacks (ordinary alloc 300) = ProgramEncoding.encodeRecords
    (SubexpNodeLiftData.liftedNodeWords p (D + 1) (SubexpPreparedQuarticSetup.modulus p 1))
  workspace : ∀ i : Fin 110, e.stacks (ordinary alloc ⟨i.val, by omega⟩) = []
  persistent_frame : ∀ i, i ∉ changedPersistent →
    e.stacks (persistent es i) = a.stacks (persistent es i)
  work_frame : ∀ i : Fin (totalStacks es), 110 ≤ i.val →
    (i.val < 128 ∨ 138 ≤ i.val) → i.val ≠ 300 → i.val < workStacks es →
    e.stacks i = a.stacks i
  controls : ∀ i, e.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem result_of_stages {er es : ℕ} (alloc : Allocation es)
    (a b c e : MainState er es) (p D : ℕ) [Fact p.Prime]
    (ha : SubexpQuarticSelectorAdapter.WorkspaceReady a)
    (hr : SubexpMainPreparedRings.SelectedResult (ringAllocation alloc)
      (SubexpQuarticSelectorAdapter.result a p) b p D)
    (hn : SubexpMainFieldNodes.Result (nodeAllocation alloc) b c p (D + 1)
      (SubexpPreparedQuarticSetup.modulus p 1))
    (hc : SubexpMainFieldCache.Result (cacheAllocation alloc) c e p D) :
    Result alloc a e p D := by
  constructor
  · exact ⟨b, c, hr, hn, hc⟩
  · exact (hc.persistent_frame 15).trans ((hn.persistent_frame 15).trans
      ((hr.persistent_frame 15 (by decide)).trans
        (SubexpQuarticSelectorAdapter.result_selected a p ha)))
  · intro i
    exact (hc.persistent_frame _).trans ((hn.persistent_frame _).trans (hr.target i))
  · intro i
    exact (hc.sourceCache_frame i).trans ((hn.sourceCache_frame i).trans (hr.source i))
  · exact hc.lifted
  · exact hc.scratch
  · intro i hi
    have ht : i ∉ SubexpMainPreparedRings.targetIndices := by
      intro hmem
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hmem
      exact hi (by fin_cases j <;> decide)
    have h15 : i ≠ 15 := by rintro rfl; exact hi (by decide)
    exact (hc.persistent_frame i).trans ((hn.persistent_frame i).trans
      ((hr.persistent_frame i ht).trans (selector_persistent_frame a p ha i h15)))
  · intro i hi hbank h300 hwork
    have hne (j : Fin 301) (hj : i.val ≠ j.val) :
        i ≠ SubexpMainFieldCache.ordinary (cacheAllocation alloc) j := by
      intro h
      exact hj (congrArg (fun q : Fin (totalStacks es) => q.val) h)
    refine (hc.frame i (hne 14 (by omega)) (hne 134 (by omega))
      (hne 135 (by omega)) (hne 136 (by omega)) (hne 137 (by omega)) (hne 300 h300)).trans
      ((hn.frame i (by omega) (by omega)).trans
        ((hr.work_frame i (by omega) (by omega) hwork).trans ?_))
    rw [SubexpQuarticSelectorAdapter.result_stacks a p ha,
      Function.update_of_ne (work_ne_persistent i hwork 15)]
  · intro i
    exact (hc.controls i).trans ((hn.control i).trans
      ((hr.controls i).trans (SubexpQuarticSelectorAdapter.result_control a p i)))

/-- Every summand uses only the words selected by the corresponding actual
phase. In particular, the old selected word and old ring/node caches remain
charged, while unrelated pending/parser/threshold data are not counted. -/
noncomputable def runtimeBound {er es : ℕ} (alloc : Allocation es) (a b c : MainState er es)
    (p D : ℕ) [Fact p.Prime] : ℕ :=
  SubexpQuarticSelectorAdapter.bound p
    (a.stacks (persistent es 6)).length (a.stacks (persistent es 15)).length +
  SubexpMainPreparedRings.runtimeBound (ringAllocation alloc)
    (SubexpQuarticSelectorAdapter.result a p) p D +
  SubexpMainFieldNodes.runtimeBound (nodeAllocation alloc) b p (D + 1) +
  SubexpMainFieldCache.runtimeBound (cacheAllocation alloc) c p + 3

theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (ha : WorkspaceReady alloc a)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    ∃ b c, ∃ n ≤ runtimeBound alloc a b c p D, ∃ e,
      Eval (procedure er alloc).invoke n a e ∧ Result alloc a e p D := by
  have has := selector_ready alloc a ha
  let selected := SubexpQuarticSelectorAdapter.result a p
  obtain ⟨ns, hns, hes⟩ := SubexpQuarticSelectorAdapter.execution a p has hp
  have hps : BinaryArithmetic.toNat (selected.stacks (persistent es 6)) = p := by
    rw [selector_persistent_frame a p has 6 (by decide)]
    exact hp
  have hms : BinaryArithmetic.toNat (selected.stacks (persistent es 22)) = D + 1 := by
    rw [selector_persistent_frame a p has 22 (by decide)]
    exact hprecision
  have hxs : BinaryArithmetic.toNat (selected.stacks (persistent es 29)) = p^4 - 2 := by
    rw [selector_persistent_frame a p has 29 (by decide)]
    exact hexp
  obtain ⟨nr, hnr, b, her, hr⟩ := SubexpMainPreparedRings.selected_execution
    (ringAllocation alloc) selected p D hps hms
    (SubexpQuarticSelectorAdapter.result_selected a p has)
  obtain ⟨nn, hnn, c, hen, hn⟩ := SubexpMainFieldNodes.after_prepared
    (nodeAllocation alloc) selected b p D
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) hr hps
  have hce : ∀ i, SubexpMainFieldCache.initiallyEmpty i →
      selected.stacks (SubexpMainFieldCache.ordinary (cacheAllocation alloc) i) = [] := by
    intro i hi
    apply selector_workspace alloc a p ha ⟨i.val, by omega⟩
    rcases hi with ⟨_, hi⟩ | hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (congrArg (fun j : Fin 301 => j.val) hi))
  obtain ⟨nc, hnc, e, hec, hc⟩ := SubexpMainFieldCache.execution
    (cacheAllocation alloc) selected b c p D
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p) hr hn hce hxs
  refine ⟨b, c, ns + (nr + (nn + nc + 1) + 1) + 1, ?_, e, ?_, ?_⟩
  · unfold runtimeBound
    dsimp only [selected] at hnr
    omega
  · exact SubexpProcedureCompose.sequence_invoke _ _ hes
      (SubexpProcedureCompose.sequence_invoke _ _ her
        (SubexpProcedureCompose.sequence_invoke _ _ hen hec))
  · exact result_of_stages alloc a b c e p D has hr hn hc

theorem program_runsIn {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (ha : WorkspaceReady alloc a)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    ∃ b c e, RunsIn (program er alloc) (runtimeBound alloc a b c p D)
      (a.withPC (some (program er alloc).entry)) (e.withPC none) ∧ Result alloc a e p D := by
  obtain ⟨b, c, n, hn, e, he, hr⟩ := execution alloc a p D ha hp hprecision hexp
  refine ⟨b, c, e, ⟨n, hn, ?_⟩, hr⟩
  cases he with
  | call _ ht => exact ht

theorem primitive_execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (ha : WorkspaceReady alloc a)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p)
    (hprecision : BinaryArithmetic.toNat (a.stacks (persistent es 22)) = D + 1)
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    ∃ b c e, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * runtimeBound alloc a b c p D)
      (primitiveCfg (program er alloc) (a.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (e.withPC none)) ∧ Result alloc a e p D := by
  obtain ⟨b, c, e, ht, hr⟩ := program_runsIn alloc a p D ha hp hprecision hexp
  exact ⟨b, c, e, BitProgram.primitive_execution _ ht, hr⟩

namespace Result

variable {er es : ℕ} {alloc : Allocation es} {a e : MainState er es}
variable {p D : ℕ} [Fact p.Prime]

theorem prime (h : Result alloc a e p D) :
    e.stacks (persistent es 6) = a.stacks (persistent es 6) :=
  h.persistent_frame 6 (by decide)

theorem precision (h : Result alloc a e p D) :
    e.stacks (persistent es 22) = a.stacks (persistent es 22) :=
  h.persistent_frame 22 (by decide)

theorem exponent (h : Result alloc a e p D) :
    e.stacks (persistent es 29) = a.stacks (persistent es 29) :=
  h.persistent_frame 29 (by decide)

theorem master_frame (h : Result alloc a e p D) (i : Fin 32) :
    e.stacks (master alloc i) = a.stacks (master alloc i) := by
  apply h.work_frame
  · simp only [SubexpLayoutPorts.master_val]; omega
  · right; simp only [SubexpLayoutPorts.master_val]; omega
  · simp only [SubexpLayoutPorts.master_val]; omega
  · exact (SubexpLayoutPorts.master_below_cleanup alloc i).trans_le alloc.within

theorem selected_length (h : Result alloc a e p D) :
    (e.stacks (persistent es 15)).length = 4 * SubexpEnumerationPayload.scalarWidth p := by
  rw [h.selected, SubexpQuarticSelectorAdapter.selectedBytes_length]

theorem field_cache (h : Result alloc a e p D) :
    ∃ c, SubexpMainFieldCache.Result (cacheAllocation alloc) c e p D := by
  obtain ⟨_, c, _, _, hc⟩ := h.stages
  exact ⟨c, hc⟩

theorem cache_lengths (h : Result alloc a e p D) :
    (e.stacks (ordinary alloc 134)).length = 4 * baseWidth p 1 * (p^4 - 1) ∧
    (e.stacks (ordinary alloc 135)).length = 4 * baseWidth p 1 * (p^4 - 1) ∧
    (e.stacks (ordinary alloc 136)).length = 4 * baseWidth p 1 * (p^4 - 1) ∧
    (e.stacks (ordinary alloc 137)).length = 4 * baseWidth p 1 * (p^4 - 1) * (p^4 - 1) := by
  obtain ⟨_, hc⟩ := h.field_cache
  exact hc.cache_lengths

end Result

def BankLengths (B : ℕ) (words : Fin 6 → List Bool) : Prop :=
  (words 0).length ≤ B + 1 ∧ (words 1).length = B ∧
  (words 2).length = 4 * B ∧ (words 3).length = 4 * B ∧
  (words 4).length = 4 * B ∧ (words 5).length = B

theorem bankWords_lengths (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    BankLengths (baseWidth p (D + 1)) (SubexpPreparedRingStaging.bankWords p D coeff hc) := by
  refine ⟨(SubexpPreparedQuarticSetup.preparedData p D coeff hc).modulus.length_le,
    SubexpPreparedQuarticPrelude.widthWord_length p (D + 1),
    SubexpPreparedQuarticSetup.flat_length _, SubexpPreparedQuarticSetup.flat_length _,
    SubexpPreparedQuarticSetup.flat_length _, (SubexpPreparedQuarticSetup.minusOne p (D + 1)).property⟩

theorem Result.target_lengths {er es : ℕ} {alloc : Allocation es} {a e : MainState er es}
    {p D : ℕ} [Fact p.Prime] (h : Result alloc a e p D) :
    BankLengths (baseWidth p (D + 1))
      (fun i => e.stacks (persistent es (SubexpMainPreparedRings.targetIndex i))) := by
  simpa only [BankLengths, h.target] using bankWords_lengths p D
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)

theorem Result.source_lengths {er es : ℕ} {alloc : Allocation es} {a e : MainState er es}
    {p D : ℕ} [Fact p.Prime] (h : Result alloc a e p D) :
    BankLengths (baseWidth p 1)
      (fun i => e.stacks (SubexpMainPreparedRings.sourcePort (ringAllocation alloc) i)) := by
  simpa only [BankLengths, h.source] using bankWords_lengths p 0
    (SubexpPreparedQuarticSetup.selectedInputCoefficients p)
    (SubexpPreparedQuarticSetup.selectedInputCoefficients_value p)

end SubexponentialSAT.SubexpMainCacheSetup

end OAI.Algorithms
