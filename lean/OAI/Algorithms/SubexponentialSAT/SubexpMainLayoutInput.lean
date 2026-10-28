import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainParameterValues
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssembly
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchScheduledExecution

namespace OAI.Algorithms

/-!
# The actual sparse leaf at the layout input

The dimension encoded in the machine state is proved equal to the typed
leaf's dimension. Transport along that equality preserves its exact bytes;
no sorting or change of variables is inserted at this boundary.
-/

namespace SubexponentialSAT.SubexpMainLayoutInput

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpPackingParameters
open SubexpMainInvariant (Stored Invariant)
open SubexpLayoutPorts (Allocation ordinary)

attribute [local simp] Fin.coe_ofNat_eq_mod

def castLeaf {n m : ℕ} (h : n = m) (G : SubexpLeafData.Leaf n) :
    SubexpLeafData.Leaf m := h ▸ G

theorem castLeaf_bytes {n m : ℕ} (h : n = m) (G : SubexpLeafData.Leaf n) :
    ExecQuantitativeSparsify.encodeRawFormula (castLeaf h G) =
      ExecQuantitativeSparsify.encodeRawFormula G := by
  cases h
  rfl

theorem castLeaf_sparse {n m k B : ℕ} (h : n = m) (G : SubexpLeafData.Leaf n)
    (hG : SubexpLeafSemantics.Sparse k B G) :
    SubexpLeafSemantics.Sparse k B (castLeaf h G) := by
  cases h
  exact hG

theorem castLeaf_no_empty {n m : ℕ} (h : n = m) (G : SubexpLeafData.Leaf n)
    (hG : [] ∉ G) : [] ∉ castLeaf h G := by
  cases h
  exact hG

theorem raw_bytes {n : ℕ} (G : SubexpLeafData.Leaf n) :
    ExecQuantitativeSparsify.encodeRawFormula G =
      Encoding.encodeList SubexpClauseRowProgram.clauseBytes G := by
  unfold ExecQuantitativeSparsify.encodeRawFormula
  rw [ExecSparsifyEncoding.encodeList_map]
  rfl

/-- Every premise consumed by the native layout, with the leaf transported
only along the proved equality of its ambient variable count. -/
structure Ready {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (n k T : ℕ) (G : SubexpLeafData.Leaf n) : Prop where
  variableCount : SubexpLayoutConstruction.variableCount
    (SubexpMainLayout.Factors.sourceInputs alloc a) = n
  ell_pos : 0 < CounterPrograms.value
    (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell
  width : CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤
    (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus.length
  modulus_pos : 0 < BinaryArithmetic.toNat
    (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus
  dimension : SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) =
    ChunkPartition.count
      (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a))
      (CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell)
  capacity : 2 ^ CounterPrograms.value
    (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤ p n
  sparse : SubexpLeafSemantics.Sparse k (DyadicSchedule.B k T n)
    (castLeaf variableCount.symm G)
  no_empty : [] ∉ castLeaf variableCount.symm G
  leafBytes : (SubexpMainLayout.Factors.sourceInputs alloc a).leaf =
    Encoding.encodeList SubexpClauseRowProgram.clauseBytes (castLeaf variableCount.symm G)
  delta : 1 + CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell *
    DyadicSchedule.B k T n ≤ DyadicSchedule.delta k T n
  metadata : ∀ i, CounterPrograms.value
    (a.stacks (SubexpMainProgram.persistent es (SubexpMainAssignment.metadataIndex i))) =
    (![r n, (p n)^4 - 1, DyadicSchedule.delta k T n,
      SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)] :
      Fin 4 → ℕ) i
  empty : ∀ i : Fin 672, a.stacks (ordinary alloc i) = []
  prime : CounterPrograms.value (a.stacks (SubexpMainProgram.persistent es 6)) = p n
  colors : CounterPrograms.value (a.stacks (SubexpMainProgram.persistent es 21)) = r n
  Q : CounterPrograms.value (a.stacks (SubexpMainProgram.persistent es 17)) = (p n)^4 - 1
  R : CounterPrograms.value (a.stacks (SubexpMainProgram.persistent es 25)) = DyadicSchedule.R k T n
  precision : BinaryArithmetic.toNat (a.stacks (SubexpMainProgram.persistent es 22)) =
    SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) + 1
  exponent : BinaryArithmetic.toNat (a.stacks (SubexpMainProgram.persistent es 29)) = (p n)^4 - 2

variable {cfg : Config} {er n B : ℕ} {hr : 32 ≤ workRegs er}
variable {F : SAT.CNF (Fin n)} {a : MainState er (mainExtraStacks cfg)}

theorem ready_from_boot (alloc : Allocation (mainExtraStacks cfg))
    (run : SubexpMainBoot.Run cfg hr F) (stored : Stored cfg run.setupOutput B a)
    (good : GoodInput n) (G : SubexpLeafData.Leaf n)
    (valid : SubexpMainAssembly.validLeaf cfg n G) (no_empty : [] ∉ G)
    (leaf : a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 9) =
      ExecQuantitativeSparsify.encodeRawFormula G)
    (empty : ∀ i : Fin 672, a.stacks (ordinary alloc i) = []) :
    Ready alloc a n cfg.k cfg.T G := by
  have hn := SubexpMainParameterValues.sourceInputs_variableCount alloc run stored
  obtain ⟨hell, hwidth, hp, hD, hcap, hdelta⟩ :=
    SubexpMainParameterValues.sourceInputs_ready alloc run stored good
  have hs := SubexpMainParameterValues.scalarValues run stored
  refine ⟨hn, hell, hwidth, hp, hD, hcap,
    castLeaf_sparse hn.symm G valid.1, castLeaf_no_empty hn.symm G no_empty,
    ?_, hdelta, SubexpMainParameterValues.sourceInputs_metadata alloc run stored,
    empty, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [SubexpMainParameterValues.sourceInputs_leaf, leaf, ← castLeaf_bytes hn.symm G]
    exact raw_bytes _
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.prime
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.colors
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word, DyadicSchedule.Q,
      SubexpParameters.sizeQ] using hs.Q
  · simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.R
  · rw [SubexpMainParameterValues.sourceInputs_dimension alloc run stored]
    simpa only [main_project_word] using hs.precision
  · simpa only [main_project_word] using hs.inverseExponent

/-- The parser transfer establishes the actual source bytes and all 672
ordinary empty inputs, while preserving the same setup state and cache cap. -/
theorem ready_transferred (alloc : Allocation (mainExtraStacks cfg))
    (halloc : alloc.ordinaryCount = helperSize cfg)
    (run : SubexpMainBoot.Run cfg hr F) (base : MainState er (mainExtraStacks cfg))
    (invariant : Invariant cfg run.setupOutput B base) (good : GoodInput n)
    (G : SubexpLeafData.Leaf n) (valid : SubexpMainAssembly.validLeaf cfg n G)
    (no_empty : [] ∉ G) (tail : List Bool) :
    Ready alloc (transferredData (leafInput base tail
      (ExecQuantitativeSparsify.encodeRawFormula G))) n cfg.k cfg.T G := by
  apply ready_from_boot alloc run
    (SubexpMainInvariant.stored_transferred_input base invariant.toStored tail _)
    good G valid no_empty
  · exact (transfer_leafInput base tail _ invariant.leaf).1
  · have hs := SubexpMainReady.transferred_ready (helperSize cfg)
      (SubexpMainInvariant.helper_within cfg)
      (leafInput base tail (ExecQuantitativeSparsify.encodeRawFormula G))
      (SubexpMainReady.leafInput_ready (helperSize cfg)
        (SubexpMainInvariant.helper_within cfg) base tail
        (ExecQuantitativeSparsify.encodeRawFormula G) invariant.storage)
    intro i
    apply hs.2
    change i.val < helperSize cfg
    have hi := i.isLt
    have ha := alloc.enough
    omega

/-- Run the actual fixed layout program from the proved input facts. The
result retains all concrete intermediate states and the measured stage sum. -/
theorem execution {er es n k T : ℕ} (alloc : Allocation es) (hregs : 16 ≤ er)
    (a : MainState er es) (G : SubexpLeafData.Leaf n)
    [Fact (p n).Prime] [NeZero (r n)]
    (input : Ready alloc a n k T G) (good : GoodInput n) (hk : 1 ≤ k) :
    let hr : 0 < r n := goodInput_s_pos good
    let hQ : 0 < (p n)^4 - 1 := DyadicSchedule.Q_pos n
    let leaf := castLeaf input.variableCount.symm G
    let hv := SubexpLayoutConstruction.family_valid
      (SubexpMainLayout.Factors.sourceInputs alloc a)
      input.modulus_pos input.ell_pos input.width input.dimension
    let scopes := SubexpLayoutScopeOrder.orderedScopes
      (SubexpMainLayout.Factors.sourceInputs alloc a) leaf input.sparse.clause_sets_nodup input.ell_pos
    ∃ hd : ∀ v : Fin (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)),
        Subexp.IncidencePlanSpec.degree scopes v.val ≤ DyadicSchedule.delta k T n,
      ∃ factorState assignmentState start coefficientState packingState middle out steps,
        ∃ result : SubexpMainLayoutExecution.Result hregs alloc a middle out
          (p n) (r n) (DyadicSchedule.delta k T n) (DyadicSchedule.R k T n)
          (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))
          hr hQ scopes hd
          (SubexpLayoutConstruction.tables (SubexpMainLayout.Factors.sourceInputs alloc a) hv leaf),
          steps ≤ SubexpMainLayoutPrefix.runtimeBound alloc a factorState assignmentState hv leaf
            input.sparse.clause_sets_nodup input.ell_pos (r n) ((p n)^4 - 1) (DyadicSchedule.delta k T n) +
            SubexpMainLayoutChoices.tailBound alloc hregs a start coefficientState packingState middle result.choices +
            SubexpMainLayoutRows.runtimeBound (List.ofFn result.choices.coefficients)
              result.choices.packing.packing scopes hd result.rows + 2 ∧
          SubexpMainLayoutChoices.EntryFacts alloc a packingState ∧
          Eval (SubexpMainLayoutProgram.procedure er hregs alloc).invoke steps a out := by
  exact SubexpMainLayoutExecution.execution alloc hregs a (p n) (r n)
    (DyadicSchedule.delta k T n) (DyadicSchedule.R k T n) k (DyadicSchedule.B k T n)
    (goodInput_s_pos good) (DyadicSchedule.Q_pos n)
    (Subexp.LocalBasisBatchScheduleBounds.scheduled_two_ne_zero n)
    input.ell_pos input.width input.modulus_pos (castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.leafBytes input.dimension input.capacity hk
    input.sparse.width input.sparse.occurrences input.no_empty input.delta input.metadata
    input.empty input.prime input.colors input.Q input.R input.precision input.exponent

end SubexponentialSAT.SubexpMainLayoutInput

end OAI.Algorithms
