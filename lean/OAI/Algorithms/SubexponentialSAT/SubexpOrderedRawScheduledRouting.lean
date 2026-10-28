import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawScheduledEnumeration
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalLayoutRows
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentRouting
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSizes

namespace OAI.Algorithms

/-! The scheduled node router uses the colors, scope order, and Boolean
tables of the exact physical factor system selected for reconstruction. -/

namespace SubexponentialSAT.SubexpOrderedRawScheduledRouting

open SubexpMainProgram SubexpSetupProgram SubexpLayoutSpec
open SubexpPackingParameters SubexpMainScheduledLayout
open SubexpMainInvariant (Stored)
open SubexpLayoutPorts (Allocation)

local instance scheduledPrime (n : ℕ) : Fact (p n).Prime := ⟨p_prime n⟩

variable {cfg : Config} {er n B : ℕ} {hrBoot : 32 ≤ workRegs er} {hregs : 16 ≤ er}
variable {F : SubexpOrderedRawPrefix.Formula n} {alloc : Allocation (mainExtraStacks cfg)}
variable {a : MainState er (mainExtraStacks cfg)}
variable (boot : SubexpOrderedRawBoot.Run cfg hrBoot F) (initial : Stored cfg boot.setupOutput B a)
variable (ready : DyadicSchedule.Ready cfg.k cfg.T n)
variable {G : SubexpLeafData.Leaf n}
variable (input : SubexpMainLayoutInput.Ready alloc a n cfg.k cfg.T G)
variable [NeZero (r n)]
variable (actual : Run alloc hregs a G input ready)

theorem factorWords_eq : SubexpMainMomentRouting.factorWords actual.result =
    (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual).color := by
  simp only [SubexpOrderedRawScheduledReconstruction.systemLayout,
    SubexpMainPhysicalLayoutRows.color]
  rfl

variable {initialized : MainState er (mainExtraStacks cfg)}
variable (hi : SubexpMainNodeInitialization.Result alloc
  (SubexpMainNodeSetup.prepared alloc actual.out) initialized
  (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)))

include hi in
theorem assignment_prefix
    (packets : Fin (scopes input).length → SubexpTemplateFactors.Factor (p n)
      (SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a))) :
    SubexpMainMomentData.store alloc initialized 258 =
      SubexpFactorRoutingTraversal.words
        (Subexp.RawTemplateRefinement.items (List.finRange (scopes input).length)
          (SubexpOrderedRawScheduledReconstruction.systemLayout boot initial ready input actual).color
          packets) ++ SubexpMainMomentRouting.suffix actual.result := by
  rw [← factorWords_eq boot initial ready input actual]
  exact SubexpMainMomentRouting.assignment_prefix actual.result hi packets

include hi actual in
theorem word_width : (SubexpMainMomentData.store alloc initialized 260).length =
    ((p n)^4 - 1) * r n :=
  SubexpMainMomentRouting.word_width actual.result hi

include hi in
theorem metadata : SubexpMainMomentData.store alloc initialized 269 =
    Subexp.SupportSelectionProgram.metadataTable actual.result.choices.packing.packing :=
  SubexpMainMomentRouting.metadata actual.result hi

theorem position (i : Fin ((p n)^4 - 1)) :
    (SubexpMainLayoutEnumeration.context actual.result i).position.val = i.val := rfl

/-- The incidence index follows the exact encounter-order scope. -/
noncomputable def scopeIndex (e : Fin (scopes input).length) :
    Fin ((scopes input).get e).length ≃
      {v // v ∈ (SubexpOrderedRawScheduledReconstruction.system input).scope e} :=
  SubexpMainPhysicalTables.scopeIndex
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension e

omit [NeZero (r n)] in
theorem scopeIndex_value (e : Fin (scopes input).length)
    (i : Fin ((scopes input).get e).length) :
    ((scopeIndex input e i).val).val = ((scopes input).get e).get i :=
  SubexpMainPhysicalTables.scopeIndex_value
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension e i

omit [NeZero (r n)] in
theorem table_count : (tables input).length = (scopes input).length :=
  SubexpMainLayoutSizes.table_count input

omit [NeZero (r n)] in
theorem table_answers (e : Fin (scopes input).length) :
    ((tables input).getD e.val []).length = (p n)^((scopes input).get e).length := by
  rw [SubexpMainLayoutSizes.tables_eq input]
  have he : e.val < (SubexpLeafScopeOrder.rawScopes
      (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
      input.sparse.clause_sets_nodup input.ell_pos).length := e.isLt
  simpa [he] using SubexpMainPhysicalTables.table_length
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.capacity input.dimension e

omit [NeZero (r n)] in
/-- The producer's answer bits become the same ordered rows used in the
physical system's interpolation theorem. -/
theorem attachedRows {C : Type*} (zero one : C) (e : Fin (scopes input).length) :
    SubexpRankedTable.attachAnswers zero one ((tables input).getD e.val []) =
      SubexpLeafTables.orderedRows (SubexpOrderedRawScheduledReconstruction.system input) e
        (scopeIndex input e) zero one := by
  have hp : BinaryArithmetic.toNat
      (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus = p n := by
    rw [SubexpMainParameterValues.sourceInputs_modulus_word]
    simpa only [CounterPrograms.value_eq_toNat] using input.prime
  exact SubexpMainPhysicalTables.produced_attachedRows _ (family input)
    (SubexpMainLayoutInput.castLeaf input.variableCount.symm G)
    input.sparse.clause_sets_nodup input.ell_pos input.dimension hp input.capacity zero one e

end SubexponentialSAT.SubexpOrderedRawScheduledRouting

end OAI.Algorithms
