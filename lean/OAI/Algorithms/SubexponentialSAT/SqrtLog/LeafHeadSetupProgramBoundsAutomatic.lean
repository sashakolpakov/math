import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsProduced

namespace OAI.Algorithms

/-! Explicit polynomial resource caps for the actual head loop. These are
proof-side upper bounds, not additional inputs or precomputed statistics. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram

def payloadWidth (n S E : ℕ) : ℕ := 4*n+20*S^2+4*E+7

def traceStateCap (A0 n S E r K : ℕ) : ℕ :=
  A0+r+1+(2*(r*payloadWidth n S E)+2)*K

def traceStepCap (A0 n S D E r K : ℕ) : ℕ :=
  traceStateCap A0 n S E r K+5*S^2+S+D+E+r*payloadWidth n S E+K

 theorem automatic_costTrace_bound (entry : SubexponentialSAT.StructuredCalls.Cmd 16 256) (base : Data)
    (n N D W : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B A0 r S E K : ℕ)
    {z0 : ℕ} {tables : List HeadTable} {costs : List ℕ} {a f : Data}
    (trace : CostTrace entry base n N D W rows low Rel T B z0 [[]] tables costs a f)
    (produced : ProducedHeads base n N D rows low Rel B z0 tables)
    (ha : WordBound A0 a) (hsize : n ≤ rows.length)
    (hr : z0+tables.length ≤ r) (hK : (tables.map fun h=>h.buckets.length).prod ≤ K)
    (hS : ∀ u ≤ r,preparationSize n N rows low W u ≤ S)
    (hE : ∀ u ≤ r,matrixEnvelope (base.stacks 141) T B D n (selectedHeads n rows low u).length ≤ E) :
    costs.sum ≤ tables.length*(100000000*(traceStepCap A0 n S D E r K+1)^4) ∧
      WordBound (traceStateCap A0 n S E r K) f := by
  apply initial_costTrace_bound entry base n N D W rows low Rel T B
    (traceStateCap A0 n S E r K) (traceStepCap A0 n S D E r K) r S E K trace produced
    (wordBound_mono ha (by unfold traceStateCap; omega)) hsize
    (by unfold traceStateCap; omega) hr hK
    (by unfold traceStateCap payloadWidth; omega)
    (by unfold traceStepCap payloadWidth; omega)
    (by unfold traceStepCap; omega) (by unfold traceStepCap; omega)
    (by unfold traceStepCap; omega) (by unfold traceStepCap; omega)
    (by unfold traceStepCap; omega) hS hE

 theorem automatic_time_bound (entry : SubexponentialSAT.StructuredCalls.Cmd 16 256) (base : Data)
    (n N D W : ℕ) (rows : List (List Bool)) (low : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (T B A0 r S E K : ℕ)
    {z0 : ℕ} {tables : List HeadTable} {costs : List ℕ} {a f : Data} (t : ℕ)
    (trace : CostTrace entry base n N D W rows low Rel T B z0 [[]] tables costs a f)
    (produced : ProducedHeads base n N D rows low Rel B z0 tables)
    (ht : t=costs.sum+2*tables.length+2)
    (ha : WordBound A0 a) (hsize : n ≤ rows.length)
    (hr : z0+tables.length ≤ r) (hK : (tables.map fun h=>h.buckets.length).prod ≤ K)
    (hS : ∀ u ≤ r,preparationSize n N rows low W u ≤ S)
    (hE : ∀ u ≤ r,matrixEnvelope (base.stacks 141) T B D n (selectedHeads n rows low u).length ≤ E) :
    t ≤ r*(100000000*(traceStepCap A0 n S D E r K+1)^4+2)+2 := by
  have hc := (automatic_costTrace_bound entry base n N D W rows low Rel T B A0 r S E K
    trace produced ha hsize hr hK hS hE).1
  have hh : tables.length ≤ r := by omega
  have hc' := hc.trans (Nat.mul_le_mul_right
    (100000000*(traceStepCap A0 n S D E r K+1)^4) hh)
  rw [ht]
  nlinarith only [hc',hh]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end

end OAI.Algorithms
