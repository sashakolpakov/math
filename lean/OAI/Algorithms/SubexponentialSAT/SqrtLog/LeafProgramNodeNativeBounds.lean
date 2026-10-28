import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeDense
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsNode

namespace OAI.Algorithms

/-! The head time is bounded from its actual CostTrace and typed input sizes. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
open LeafHeadSetupProgram.Bounds SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def headBudget (s : HeadInputs) (S0 rCap S E K : ℕ) : ℕ :=
  20000*(S0+1)^4+
    (rCap*(100000000*(traceStepCap (2*(S0+1)^2+3) s.n S s.D E rCap K+1)^4+2)+2)+
    (100000+1007*LeafHeadSetupProgram.cleanupPorts.length)*
      (traceStateCap (2*(S0+1)^2+3) s.n S E rCap K+1)^2+1

theorem HeadEvidence.steps_le {s : HeadInputs} {a b : NodeNative.Data}
    (h : HeadEvidence s a b) (S0 rCap S E K : ℕ)
    (ha : WordBound S0 (Native.project a))
    (hn : s.n ≤ S0) (hr : s.r ≤ S0) (hnode : s.node.val ≤ S0)
    (hb : (SubexponentialSAT.Encoding.encodeList id s.records).length ≤ S0)
    (hh : s.height.length ≤ S0) (hR : s.R ≤ S0) (hw : s.width.length ≤ S0)
    (haddress : s.node.val*s.r+s.r ≤ rCap)
    (hK : (h.tables.map fun h=>h.buckets.length).prod ≤ K)
    (hS : ∀ u ≤ rCap,preparationSize s.n s.N s.rows s.low (s.Q*s.r) u ≤ S)
    (hE : ∀ u ≤ rCap,matrixEnvelope (a.stacks 141) s.columnTime s.columnLength s.D
      s.n (selectedHeads s.n s.rows s.low u).length ≤ E) :
    h.steps ≤ headBudget s S0 rCap S E K := by
  obtain ⟨loopEnd,rf,ht,hend,hsteps,hout,hnout⟩ := h.paid
  have hlen : h.words.length=(unary s.R).length := by simpa [unary] using h.cache.1
  have hwords : ∀ word∈h.words,word.length=s.width.length := h.cache.2.1
  have htrace : CostTrace Native.entry
      (nodeStart (Native.project a) h.ra h.rd h.rc s.r s.node.val s.records s.height (unary s.R) s.width h.words)
      s.n s.N s.records.length (s.Q*s.r) s.rows s.low s.relation s.columnTime s.columnLength
      (s.node.val*s.r) [[]] h.tables h.costs
      (nodeStart (Native.project a) h.ra h.rd h.rc s.r s.node.val s.records s.height (unary s.R) s.width h.words)
      loopEnd := by simpa only [Native.start,Native.Inputs.records_length] using ht
  have hprod : ProducedHeads
      (nodeStart (Native.project a) h.ra h.rd h.rc s.r s.node.val s.records s.height (unary s.R) s.width h.words)
      s.n s.N s.records.length s.rows s.low s.relation s.columnLength (s.node.val*s.r) h.tables := by
    simpa only [Native.start,Native.Inputs.records_length] using h.produced
  have hbnd := nodeCost_bound Native.entry (Native.project a) h.ra h.rd h.rc rf
    s.n s.N (s.Q*s.r) s.r s.node.val s.columnTime s.columnLength S0 rCap S E K
    s.records s.rows s.low s.height (unary s.R) s.width h.words h.tables h.costs loopEnd s.relation
    ha hn hr hnode hb hh (by simpa [unary] using hR) hw hlen hwords htrace hprod hout
    (by have := s.rows_length; omega) (by simpa only [h.count] using haddress) hK hS
    (by
      intro u hu
      have hx := Native.start_low s (Native.project a) h.ra h.rd h.rc h.words 141 (by decide)
      change (nodeStart (Native.project a) h.ra h.rd h.rc s.r s.node.val s.records s.height
        (unary s.R) s.width h.words).stacks 141=a.stacks 141 at hx
      simpa only [hx,Native.Inputs.records_length] using hE u hu)
  simp only [Native.Inputs.records_length] at hbnd
  exact hsteps.trans (Nat.add_le_add_right hbnd 1)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end

end OAI.Algorithms
