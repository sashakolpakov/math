import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentStatics
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingAssignment
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalTables

namespace OAI.Algorithms

/-! The node router reads the same assignment, factor order, metadata,
and table answers that the layout program produced. The unused assignment
suffix is retained explicitly; no reordering or fresh assignment is used. -/

namespace SubexponentialSAT.SubexpMainMomentRouting

noncomputable section

open SubexpMainProgram Subexp MulticolorTypes
open SubexpLayoutPorts (Allocation master)
open SubexpMainMomentData (store)

section Stored

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
  {alloc : Allocation es} {a middle layoutOut initialized : MainState er es}
  {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ R D hr hQ scopes hd tables)
  (hi : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc layoutOut) initialized D)

def assignment : SubexpTypeVariance.Assignment (Fin D) (Fin scopes.length) r (p^4 - 1) Δ :=
  NaturalAssignment.naturalAssignment (IncidencePlanSpec.pattern D scopes)
    (IncidencePlanSpec.slots D Δ scopes hd) h.choices.first h.choices.tail
    (List.finRange D) (AssignmentEnumeration.seedIndices
      (List.finRange D) (List.finRange scopes.length) Δ)

def factorWords (e : Fin scopes.length) : Word r (p^4 - 1) := assignment h (.inl e)

def suffix : List Bool :=
  SubexpFactorRoutingAssignment.assignmentSuffix (List.finRange D) (assignment h)

include hi in
theorem assignment_prefix (packets : Fin scopes.length → SubexpTemplateFactors.Factor p D) :
    store alloc initialized 258 =
      SubexpFactorRoutingTraversal.words
        (RawTemplateRefinement.items (List.finRange scopes.length) (factorWords h) packets) ++
      suffix h := by
  have hm := (SubexpMainMomentData.static_frame hi 2).trans h.assignment_master
  have hs : SubexpAssignmentStaging.assignedBytes Δ D scopes hd h.choices.first h.choices.tail =
      (ReadPlan.seedRows (List.finRange D) (List.finRange scopes.length) (assignment h)).flatten :=
    AssignmentSerialization.naturalValues_bytes_eq_seedRows
      (IncidencePlanSpec.pattern D scopes) (IncidencePlanSpec.slots D Δ scopes hd)
      h.choices.first h.choices.tail (List.finRange D) (List.finRange scopes.length)
      (List.nodup_finRange D) (List.nodup_finRange scopes.length)
  have hp := SubexpFactorRoutingAssignment.seedRows_factor_prefix
    (List.finRange D) (List.finRange scopes.length) (assignment h)
    (fun e => (packets e).map SubexpBlueprintRows.Row.packet)
  exact hm.trans (hs.trans (by
    simpa only [SubexpFactorRoutingAssignment.factorItems,
      RawTemplateRefinement.items, SubexpTemplateFactors.encode, factorWords, suffix] using hp))

include h hi in
theorem word_width : (store alloc initialized 260).length = (p^4 - 1) * r := by
  have hm := (SubexpMainMomentData.static_frame hi 4).trans (h.saved_master 4 (by decide))
  exact (congrArg List.length hm).trans h.choices.prefixResult.width

include h hi in
theorem metadata : store alloc initialized 269 =
    SupportSelectionProgram.metadataTable h.choices.packing.packing :=
  (SubexpMainMomentData.static_frame hi 13).trans (h.packing_master 2)

theorem position (i : Fin (p^4 - 1)) :
    (SubexpMainLayoutEnumeration.context h i).position.val = i.val := rfl

end Stored

section Color

variable {er es p k r Δ D : ℕ} {τ : ℚ} [Fact p.Prime] [NeZero r]
  {alloc : Allocation es} {a middle layoutOut : MainState er es}
  {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (c : SubexpLayoutSpec.Parameters p k Δ r τ) (h4 : c.h = 4)
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ c.R D hr hQ scopes hd tables)
  (hP : (IncidencePlanSpec.pattern D scopes).Bounded k Δ)
  (hsize : c.Dstar ≤ D)
  (hthreshold : (Fintype.card (UniversalType r (p^4 - 1) Δ) : ℚ)^3 *
    (1 + (Δ * k : ℕ)) ≤ τ^2 * c.Dstar)
  (htail : SpectralRank.normalizedTail r (p^4 - 1 - 1)
    (TailInterval.intervalStart r (p^4 - 1) c.R) c.R ≤ τ / (Δ : ℚ))

theorem factorWords_color (e : Fin scopes.length) (i : Fin (p^4 - 1)) :
    factorWords h e i =
      (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail).color e i := rfl

end Color

section Tables

variable {p : ℕ} [Fact p.Prime]
  (x : SubexpLayoutConstruction.Inputs)
  (hv : SubexpClauseFamilyProgram.Valid (SubexpLayoutConstruction.familyInputs x)
    (SubexpLayoutConstruction.dimension x) (SubexpLayoutConstruction.variableCount x))
  (G : SubexpLeafData.Leaf (SubexpLayoutConstruction.variableCount x))
  (hG : (G.map ExecCNF.clauseSet).Nodup)
  (hell : 0 < CounterPrograms.value x.counts.ell)
  (hD : SubexpLayoutConstruction.dimension x =
    ChunkPartition.count (SubexpLayoutConstruction.variableCount x)
      (CounterPrograms.value x.counts.ell))
  (hp : BinaryArithmetic.toNat x.counts.modulus = p)
  (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p)

include hp hD hcap in
theorem table_count : (SubexpLayoutConstruction.tables x hv G).length =
    (SubexpLayoutScopeOrder.orderedScopes x G hG hell).length := by
  rw [SubexpLayoutTableOrder.table_payloads_eq x hv G hG hell hD hp hcap]
  change (SubexpLeafTableOrder.orderedTables G hG hell hcap).length =
    (SubexpLeafScopeOrder.rawScopes G hG hell).length
  rw [SubexpMainPhysicalTables.orderedTables_eq G hG hell hcap hD, List.length_ofFn]

include hp hD hcap in
theorem table_answers (e : Fin (SubexpLayoutScopeOrder.orderedScopes x G hG hell).length) :
    ((SubexpLayoutConstruction.tables x hv G).getD e.val []).length =
      p ^ ((SubexpLayoutScopeOrder.orderedScopes x G hG hell).get e).length := by
  have he := SubexpMainPhysicalTables.produced_table_getD x hv G hG hell hD hp hcap e
  exact (congrArg List.length he).trans (SubexpMainPhysicalTables.table_length G hG hell hcap hD e)

end Tables

end
end SubexponentialSAT.SubexpMainMomentRouting

end OAI.Algorithms
