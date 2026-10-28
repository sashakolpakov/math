import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentRouting
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentHeaders
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentReadback
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkerEvidence
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCanonicalJet

namespace OAI.Algorithms

/-! The concrete arguments of the node worker, read from the actual Main
layout and initialization results. These aliases retain the physical
factor, scope, coordinate, node, and cache orders. -/

namespace SubexponentialSAT.SubexpMainNodeArguments

noncomputable section

open SubexpMainProgram Subexp SubexpLiftRing SubexpSelectedConversions
open SubexpLayoutPorts (Allocation ordinary)
open SubexpMainMomentData (store target)

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

def source : Prepared p 0 := h.rows.cacheFacts.source

def rowExpr : ℕ → ℕ → ℕ → SubexpTaylorRowCorrectness.RowExpr p :=
  SubexpDenseRowTableSemantics.expressionFor (source h)
    (List.ofFn h.choices.coefficients) h.rows.cacheFacts.inverse
    h.rows.cacheFacts.negative h.rows.cacheFacts.difference
    h.choices.packing.packing scopes hd

def theta (i : Fin (p^4-1)) : SubexpTaylorRow.Code p (D+1) :=
  SubexpMainMomentReadback.nodeCode p D i

def cache : List (List (SubexpFactorPacketProvenance.Code p D)) := h.rows.lagrangeRows

def factor (i : Fin (p^4-1)) (e : Fin scopes.length) :=
  SubexpNodePacketInputs.factor (source h) (target p D) (theta (D := D) i) R
    (store alloc initialized 129) (SubexpMainMomentData.context_masters h hi).sourceWidth
    (cache h) (target p D).zero (target p D).one (rowExpr h) scopes tables e

theorem source_eq : source h = SubexpMainRowCache.sourceData p := h.rows.cacheFacts.source_eq

theorem theta_word (i : Fin (p^4-1)) :
    SubexpNodeIndexSemantics.thetaWord p D i = SubexpTaylorRow.flat (theta (D := D) i) := by
  change SubexpNodeIndexSemantics.thetaWord p D i =
    SubexpQuarticFlatMul.flat (SubexpMainMomentReadback.nodeCode p D i)
  rw [SubexpMainRowCache.flat_eq_encode]
  exact (SubexpMainMomentReadback.nodeCode_word p D i).symm

theorem cache_length : (cache h).length = p :=
  SubexpMainLagrangeCache.rows_length h.rows.lagrangeCorrect

theorem cache_large : p ≤ (cache h).length := (cache_length h).ge

theorem rows_eq :
    SubexpDenseRowTableSemantics.expressionRows (rowExpr h) D 0 scopes = h.expressions := rfl

include hi in
theorem row_master (hvalid : ∀ C ∈ scopes, ∀ v ∈ C, v < D) :
    store alloc initialized 255 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat
      (SubexpNodeCacheTyped.rows p (D+1) (source h) R
        (SubexpDenseRowTableSemantics.expressionRows (rowExpr h) D 0 scopes)) :=
  (SubexpMainMomentData.row_frame hi).trans (h.row_master hvalid)

include hi in
theorem node_master : store alloc initialized 125 = ProgramEncoding.encodeRecords
    (SubexpNodeLiftData.liftedNodeWords p (D+1) (source h).modulus) := by
  rw [source_eq h]
  exact SubexpMainMomentData.nodes h hi

theorem target_zero_canonical : SubexpCanonicalWords.CanonicalQuad p (D+1) (target p D).zero :=
  SubexpCanonicalWords.prepareZero_canonical p (D+1)

include hi in
theorem packet_masters :
    SubexpNodeBlueprintWorkspace.PacketMasters (store alloc initialized) scopes tables
      ((cache h).map (List.map SubexpQuarticFlatNeg.flat))
      (SubexpQuarticFlatNeg.flat (target p D).zero)
      (SubexpQuarticFlatNeg.flat (target p D).one) :=
  SubexpMainMomentStatics.packet_masters h hi

end
end SubexponentialSAT.SubexpMainNodeArguments

end OAI.Algorithms
