import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketInputs
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentReadback
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalLayoutRows
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalTables

namespace OAI.Algorithms

/-!
# Local semantics of the generated numeric factor packets

The source rows come from the actual layout choices. Origins are the
computed residues of their shifted constant coefficients, and the Boolean
rows retain the physical scope and descending label order. No equality of
whole packets, factor values, or output jets is a premise.
-/

noncomputable section

namespace SubexponentialSAT.SubexpNodePacketSemantics

open SubexpSelectedConversions SubexpLayoutSpec SubexpMainProgram Subexp
open SubexpFactorPacketProvenance (Code)
open SubexpLiftRing

section Tables

variable {p D : ℕ} [Fact p.Prime] (target : Prepared p D)

/-- Integer labels, rather than extension-field enumeration labels, are
used when interpreting the stored Boolean table. -/
theorem orderedRows_table {F : Type*} {m : ℕ}
    (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (ix : Fin m ≃ {v // v ∈ S.scope e}) :
    SubexpTableInterpolation.tablePolynomial
      (SubexpLagrangeCacheAlgebra.integerNodes p (D + 1))
      (SubexpLagrangeCacheAlgebra.integerNodes_units p (D + 1))
      ((SubexpLeafTables.orderedRows S e ix target.zero target.one).map
        (SubexpRepresentedBuilder.mapRow (SubexpFactorPacketProvenance.decode p D))) =
      MvPolynomial.rename ix.symm
        (GlobalPolynomial.interpolatedTable S (SubexpActualRing.coordinateLift p (D + 1))
          (SubexpActualRing.coordinateLift_unitDifferences p (D + 1)) e) := by
  have hl : SubexpLeafTables.labels target.ring =
      SubexpLagrangeCacheAlgebra.integerNodes p (D + 1) := by
    funext i
    exact SubexpTableExecution.labelsProgram_correct target.ring p i
  have hdecode : target.ring.decode = SubexpFactorPacketProvenance.decode p D := by
    funext a
    rfl
  have hzero : target.ring.zeroRun.1 = target.zero := rfl
  have hone : target.ring.oneRun.1 = target.one := rfl
  simpa only [hl, hdecode, hzero, hone] using
    SubexpLeafTables.orderedRows_correct target.ring S e ix

variable (source : Prepared p 0) (theta : Code p D) (R : ℕ)
  (sourceWidth : List Bool) (hw : sourceWidth.length = baseWidth p 1)
  (cache : List (List (Code p D)))
  (expr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p)

/-- The actual generated answer bytes, with their actual attached labels,
give the interpolation polynomial of the physical factor system. -/
theorem produced_input_table
    (x : SubexpLayoutConstruction.Inputs)
    (hv : SubexpClauseFamilyProgram.Valid (SubexpLayoutConstruction.familyInputs x)
      (SubexpLayoutConstruction.dimension x) (SubexpLayoutConstruction.variableCount x))
    (leaf : SubexpLeafData.Leaf (SubexpLayoutConstruction.variableCount x))
    (hleaf : (leaf.map ExecCNF.clauseSet).Nodup)
    (hell : 0 < CounterPrograms.value x.counts.ell)
    (hD : D = ChunkPartition.count (SubexpLayoutConstruction.variableCount x)
      (CounterPrograms.value x.counts.ell))
    (hdimension : SubexpLayoutConstruction.dimension x = D)
    (hp : BinaryArithmetic.toNat x.counts.modulus = p)
    (hcap : 2 ^ CounterPrograms.value x.counts.ell ≤ p)
    (e : Fin (SubexpLeafScopeOrder.rawScopes leaf hleaf hell).length) :
    SubexpTableInterpolation.tablePolynomial
      (SubexpLagrangeCacheAlgebra.integerNodes p (D + 1))
      (SubexpLagrangeCacheAlgebra.integerNodes_units p (D + 1))
      (((SubexpNodePacketInputs.factor source target theta R sourceWidth hw cache
        target.zero target.one expr (SubexpLeafScopeOrder.rawScopes leaf hleaf hell)
        (SubexpLayoutConstruction.tables x hv leaf) e).data.rows).map
          (SubexpRepresentedBuilder.mapRow (SubexpFactorPacketProvenance.decode p D))) =
      MvPolynomial.rename (SubexpMainPhysicalTables.scopeIndex leaf hleaf hell hcap hD e).symm
        (GlobalPolynomial.interpolatedTable
          (SubexpMainPhysicalSystem.system leaf hleaf hell hcap hD)
          (SubexpActualRing.coordinateLift p (D + 1))
          (SubexpActualRing.coordinateLift_unitDifferences p (D + 1)) e) := by
  cases hdimension
  unfold SubexpNodePacketInputs.factor SubexpNodePacketInputs.factorAt
  change SubexpTableInterpolation.tablePolynomial _ _
    ((SubexpRankedTable.attachAnswers target.zero target.one
      ((SubexpLayoutConstruction.tables x hv leaf).getD e.val [])).map _) = _
  rw [SubexpMainPhysicalTables.produced_attachedRows x hv leaf hleaf hell hD hp hcap]
  exact orderedRows_table target _ e _

end Tables

section Numeric

variable {p k Δ r : ℕ} {tau : ℚ} {er es D : ℕ} [Fact p.Prime] [NeZero r]
  {alloc : SubexpLayoutPorts.Allocation es} {a middle out : MainState er es}
  {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (c : Parameters p k Δ r tau)
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle out
    p r Δ c.R D hr hQ scopes hd tables)

/-- This is the expression selected by the physical dense-row traversal. -/
def expression : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p :=
  SubexpDenseRowTableSemantics.expressionFor h.rows.cacheFacts.source
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse h.rows.cacheFacts.negative
    h.rows.cacheFacts.difference h.choices.packing.packing scopes hd

/-- A definitional alias for the producer's actual per-factor data. -/
def input (target : Prepared p D) (node : Fin (p^4 - 1))
    (sourceWidth : List Bool) (hw : sourceWidth.length = baseWidth p 1)
    (cache : List (List (Code p D))) (e : Fin scopes.length) :
    SubexpFactorPacketProvenance.Input p D p (scopes.get e).length c.R :=
  (SubexpNodePacketInputs.factor h.rows.cacheFacts.source target
    (SubexpMainMomentReadback.nodeCode p D node) c.R sourceWidth hw cache
    target.zero target.one (expression c h) scopes tables e).data

variable (h4 : c.h = 4)
  (hP : (Subexp.IncidencePlanSpec.pattern D scopes).Bounded k Δ)
  (hsize : c.Dstar ≤ D)
  (hthreshold : (Fintype.card (MulticolorTypes.UniversalType r (p^4 - 1) Δ) : ℚ)^3 *
    (1 + (Δ * k : ℕ)) ≤ tau^2 * c.Dstar)
  (htail : SpectralRank.normalizedTail r (p^4 - 1 - 1)
    (TailInterval.intervalStart r (p^4 - 1) c.R) c.R ≤ tau / (Δ : ℚ))
  (target : Prepared p D) (node : Fin (p^4 - 1))
  (sourceWidth : List Bool) (hw : sourceWidth.length = baseWidth p 1)
  (cache : List (List (Code p D)))

theorem input_row (e : Fin scopes.length) (i : Fin (scopes.get e).length)
    (v : {v // v ∈ (Subexp.IncidencePlanSpec.pattern D scopes).scope e})
    (hv : v.val.val = (scopes.get e).get i) (w : Fin D) :
    (((input c h target node sourceWidth hw cache e).sourceRows i w).map
      (SubexpRowSourceSemantics.denote h.rows.cacheFacts.source)).eval =
      (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail).row e v w := by
  change ((expression c h e.val ((scopes.get e).get i) w.val).map _).eval = _
  rw [← hv]
  exact SubexpMainLayoutSemantics.expression_denote c h4 h hP hsize hthreshold htail
    e v.val ((Subexp.IncidencePlanSpec.mem_pattern_scope D scopes v.val e).mp v.property) w

include h4 hP hsize hthreshold htail in
/-- The source-degree side condition follows from the same constructed
layout, before any lift or Taylor truncation is applied. -/
theorem input_degree (e : Fin scopes.length) (i : Fin (scopes.get e).length)
    (v : {v // v ∈ (Subexp.IncidencePlanSpec.pattern D scopes).scope e})
    (hv : v.val.val = (scopes.get e).get i) (w : Fin D) :
    ((((input c h target node sourceWidth hw cache e).sourceRows i w).map
      (SubexpRowSourceSemantics.denote h.rows.cacheFacts.source)).eval).natDegree ≤ c.R := by
  rw [input_row c h h4 hP hsize hthreshold htail target node sourceWidth hw cache e i v hv w]
  exact (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail).row_degree e v w

theorem node_residue :
    SubexpActualRing.rho p (D + 1) (Nat.succ_pos D)
      (SubexpFactorPacketProvenance.decode p D (SubexpMainMomentReadback.nodeCode p D node)) =
      (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail).node node := by
  have hn : SubexpFactorPacketProvenance.decode p D
      (SubexpMainMomentReadback.nodeCode p D node) =
      SubexpActualRing.sectionValue p (D + 1) (Nat.succ_pos D)
        (SubexpMachineNodeOrder.nodeEquiv p node).val :=
    SubexpMainMomentReadback.nodeCode_decode p D node
  rw [hn, SubexpActualRing.rho_sectionValue]
  rfl

theorem node_decode :
    SubexpFactorPacketProvenance.decode p D (SubexpMainMomentReadback.nodeCode p D node) =
      (SubexpExplicitLift.explicitLiftedLayout
        (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail)
        (D + 1) (Nat.succ_pos D)).theta node := by
  exact SubexpMainMomentReadback.nodeCode_decode p D node

theorem input_origin (e : Fin scopes.length) (i : Fin (scopes.get e).length)
    (v : {v // v ∈ (Subexp.IncidencePlanSpec.pattern D scopes).scope e})
    (hv : v.val.val = (scopes.get e).get i) (w : Fin D) :
    h.rows.cacheFacts.source.residueRing.decode
      ((input c h target node sourceWidth hw cache e).origins i w) =
      ((SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail).row e v w).eval
        ((SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail).node node) := by
  have ho := SubexpOriginCacheSemantics.origin_decode p (D + 1) h.rows.cacheFacts.source
    target.modulus target.reduction (SubexpMainMomentReadback.nodeCode p D node)
    c.R (c.R + 1) (Nat.succ_pos c.R) h.rows.cacheFacts.source.modulus sourceWidth hw
    (Nat.succ_pos D) target.reduction_spec
    (expression c h e.val ((scopes.get e).get i) w.val)
    (input_degree c h h4 hP hsize hthreshold htail target node sourceWidth hw cache e i v hv w)
  change h.rows.cacheFacts.source.residueRing.decode
      ((input c h target node sourceWidth hw cache e).origins i w) =
    (((input c h target node sourceWidth hw cache e).sourceRows i w).map
      (SubexpRowSourceSemantics.denote h.rows.cacheFacts.source)).eval.eval
      (SubexpActualRing.rho p (D + 1) (Nat.succ_pos D)
        (SubexpFactorPacketProvenance.decode p D (SubexpMainMomentReadback.nodeCode p D node))) at ho
  rw [input_row c h h4 hP hsize hthreshold htail target node sourceWidth hw cache e i v hv w,
    node_residue c h h4 hP hsize hthreshold htail node] at ho
  exact ho

end Numeric

section Physical

variable {p k Δ r : ℕ} {tau : ℚ} {er es D n ell : ℕ} [Fact p.Prime] [NeZero r]
  {alloc : SubexpLayoutPorts.Allocation es} {a middle out : MainState er es}
  {hregs : 16 ≤ er} {hr : 0 < r} {hQ : 0 < p^4 - 1}
  (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
  (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell)
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree
    (SubexpLeafScopeOrder.rawScopes G hG hell) v.val ≤ Δ}
  {tables : List (List Bool)} (c : Parameters p k Δ r tau)
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle out
    p r Δ c.R D hr hQ (SubexpLeafScopeOrder.rawScopes G hG hell) hd tables)
  (h4 : c.h = 4)
  (hP : (Subexp.IncidencePlanSpec.pattern D (SubexpLeafScopeOrder.rawScopes G hG hell)).Bounded k Δ)
  (hsize : c.Dstar ≤ D)
  (hthreshold : (Fintype.card (MulticolorTypes.UniversalType r (p^4 - 1) Δ) : ℚ)^3 *
    (1 + (Δ * k : ℕ)) ≤ tau^2 * c.Dstar)
  (htail : SpectralRank.normalizedTail r (p^4 - 1 - 1)
    (TailInterval.intervalStart r (p^4 - 1) c.R) c.R ≤ tau / (Δ : ℚ))
  (target : Prepared p D) (node : Fin (p^4 - 1))
  (sourceWidth : List Bool) (hw : sourceWidth.length = baseWidth p 1)
  (cache : List (List (Code p D)))

theorem physical_input_row (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (i : Fin ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).length) (w : Fin D) :
    (((input c h target node sourceWidth hw cache e).sourceRows i w).map
      (SubexpRowSourceSemantics.denote h.rows.cacheFacts.source)).eval =
      (SubexpMainPhysicalSystem.layout G hG hell hcap hD
        (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail)).row e
          (SubexpMainPhysicalTables.scopeIndex G hG hell hcap hD e i) w := by
  rw [SubexpMainPhysicalLayoutRows.row]
  apply input_row c h h4 hP hsize hthreshold htail target node sourceWidth hw cache
  rw [SubexpMainPhysicalLayoutRows.scopeBack_val]
  exact SubexpMainPhysicalTables.scopeIndex_value G hG hell hcap hD e i

include hcap hD h4 hP hsize hthreshold htail in
theorem physical_input_degree (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (i : Fin ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).length) (w : Fin D) :
    ((((input c h target node sourceWidth hw cache e).sourceRows i w).map
      (SubexpRowSourceSemantics.denote h.rows.cacheFacts.source)).eval).natDegree ≤ c.R := by
  rw [physical_input_row G hG hell hcap hD c h h4 hP hsize hthreshold htail
    target node sourceWidth hw cache e i w]
  exact (SubexpMainPhysicalSystem.layout G hG hell hcap hD
    (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail)).row_degree e _ w

theorem physical_input_origin (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (i : Fin ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).length) (w : Fin D) :
    h.rows.cacheFacts.source.residueRing.decode
      ((input c h target node sourceWidth hw cache e).origins i w) =
      ((SubexpMainPhysicalSystem.layout G hG hell hcap hD
        (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail)).row e
          (SubexpMainPhysicalTables.scopeIndex G hG hell hcap hD e i) w).eval
        ((SubexpMainPhysicalSystem.layout G hG hell hcap hD
          (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail)).node node) := by
  rw [SubexpMainPhysicalLayoutRows.row, SubexpMainPhysicalLayoutFields.node]
  apply input_origin c h h4 hP hsize hthreshold htail target node sourceWidth hw cache
  rw [SubexpMainPhysicalLayoutRows.scopeBack_val]
  exact SubexpMainPhysicalTables.scopeIndex_value G hG hell hcap hD e i

theorem physical_node_decode :
    SubexpFactorPacketProvenance.decode p D (SubexpMainMomentReadback.nodeCode p D node) =
      (SubexpExplicitLift.explicitLiftedLayout
        (SubexpMainPhysicalSystem.layout G hG hell hcap hD
          (SubexpMainLayoutSemantics.layout c h4 h hP hsize hthreshold htail))
        (D + 1) (Nat.succ_pos D)).theta node := by
  change SubexpFactorPacketProvenance.decode p D (SubexpMainMomentReadback.nodeCode p D node) =
    SubexpActualRing.sectionValue p (D + 1) (Nat.succ_pos D) _
  rw [SubexpMainPhysicalLayoutFields.node]
  exact SubexpMainMomentReadback.nodeCode_decode p D node

end Physical

end SubexponentialSAT.SubexpNodePacketSemantics

end

end OAI.Algorithms
