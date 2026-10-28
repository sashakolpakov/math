import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsAutomatic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsFinal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBootPolynomial
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramRun

namespace OAI.Algorithms

/-! The whole native node cost, from paid cache construction through every
head and final serialization. All observations come from the actual node
execution. The proof-side caps charge full row dimension and bucket payload. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram

 theorem nodeCost_bound (entry : Cmd 16 256) (a : Data)
    (ra : Fin 3 → Bool) (rd rc rf : Fin 8 → Bool)
    (n N W r node T B S0 rCap S E K : ℕ)
    (records rows : List (List Bool)) (low height R width : List Bool)
    (words : List (List Bool)) (tables : List HeadTable) (costs : List ℕ) (loopEnd : Data)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop)
    (ha : WordBound S0 a) (hn : n ≤ S0) (hr : r ≤ S0) (hnode : node ≤ S0)
    (hb : (SubexponentialSAT.Encoding.encodeList id records).length ≤ S0)
    (hh : height.length ≤ S0) (hR : R.length ≤ S0) (hw : width.length ≤ S0)
    (hlen : words.length=R.length) (hwords : ∀ word∈words,word.length=width.length)
    (trace : CostTrace entry (nodeStart a ra rd rc r node records height R width words)
      n N records.length W rows low Rel T B (node*r) [[]] tables costs
      (nodeStart a ra rd rc r node records height R width words) loopEnd)
    (produced : ProducedHeads (nodeStart a ra rd rc r node records height R width words)
      n N records.length rows low Rel B (node*r) tables)
    (hout : loopEnd.stacks 660=Representative.tuplesBits (enumerate tables))
    (hsize : n ≤ rows.length) (haddress : node*r+tables.length ≤ rCap)
    (hK : (tables.map fun h=>h.buckets.length).prod ≤ K)
    (hS : ∀ u ≤ rCap,preparationSize n N rows low W u ≤ S)
    (hE : ∀ u ≤ rCap,matrixEnvelope
      ((nodeStart a ra rd rc r node records height R width words).stacks 141)
      T B records.length n (selectedHeads n rows low u).length ≤ E) :
    nodeCost a ra rd rc n r node records height R width words tables costs loopEnd rf ≤
      20000*(S0+1)^4 +
      (rCap*(100000000*(traceStepCap (2*(S0+1)^2+3) n S records.length E rCap K+1)^4+2)+2) +
      (100000+1007*cleanupPorts.length)*
        (traceStateCap (2*(S0+1)^2+3) n S E rCap K+1)^2 := by
  let A0 := 2*(S0+1)^2+3
  let A := traceStateCap A0 n S E rCap K
  obtain ⟨hboot,hstart⟩ := initializeCost_polynomial a ra rd rc r node records
    height R width words S0 ha hr hnode hb hh hR hw hlen hwords
  obtain ⟨hcost,hend⟩ := automatic_costTrace_bound entry
    (nodeStart a ra rd rc r node records height R width words)
    n N records.length W rows low Rel T B A0 rCap S E K trace produced hstart
    hsize haddress hK hS hE
  have ht := automatic_time_bound entry
    (nodeStart a ra rd rc r node records height R width words)
    n N records.length W rows low Rel T B A0 rCap S E K
    (costs.sum+2*tables.length+2) trace produced rfl hstart
    hsize haddress hK hS hE
  have hSA : S0 ≤ A := by
    have h0 : S0 ≤ A0 := by dsimp [A0]; nlinarith
    exact h0.trans (by dsimp [A,traceStateCap]; omega)
  have hnA : (unary n).length ≤ A := by simpa [unary] using hn.trans hSA
  have hbytes : (Representative.tuplesBits (enumerate tables)).length ≤ A := by
    rw [←hout]
    exact hend 660
  have hvalid : ∀ heads∈enumerate tables,∀ h∈heads,
      Representative.Valid (unary n).length h := by
    simpa [unary] using enumerate_valid n tables (producedHeads_valid produced)
  have hfinal := final_cleanup_bound cleanupPorts loopEnd rf (unary n) (enumerate tables)
    A hend hnA hbytes hvalid
  unfold nodeCost
  dsimp [A,A0] at ht hfinal
  omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end

end OAI.Algorithms
