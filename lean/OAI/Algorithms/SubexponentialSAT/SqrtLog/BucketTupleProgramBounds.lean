import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramSchema
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

namespace OAI.Algorithms

/-! Explicit byte costs and a direct primitive-machine execution corollary. -/
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace Table

theorem stepCost_le (mask context : List Bool) (b : Bucket) :
    stepCost mask context b ≤ 200*(mask.length+context.length+(payload b).length+1) := by
  simp [stepCost,headBits,payload,Encoding.length_frame]
  omega

theorem cost_le (mask context : List Bool) (bs : List Bucket) :
    cost mask context bs ≤
      300*(mask.length+context.length+1)*((tableBits bs).length+1) := by
  induction bs with
  | nil => simp [cost,tableBits,Encoding.encodeList]; omega
  | cons b bs ih =>
      have hs := stepCost_le mask context b
      have hlen : (tableBits (b::bs)).length=2*(payload b).length+2+(tableBits bs).length := by
        simp [tableBits,Encoding.length_encodeList_cons]
      simp only [cost,List.map_cons,List.sum_cons] at ih ⊢
      rw [hlen]
      nlinarith [Nat.zero_le (mask.length*(payload b).length),
        Nat.zero_le (context.length*(payload b).length)]

end Table

namespace Representative

open SubexponentialSAT.SqrtLog.MomentsAssembly (HeadInput rawFrames)

theorem rawFrames_tail_le (xs : List (List Bool)) :
    (rawFrames xs.tail).length ≤ (rawFrames xs).length := by
  cases xs <;> simp [rawFrames]

theorem headCost_le (h : HeadInput) (n : ℕ) (hv : Valid n h) :
    headCost h n ≤ 100*(h.bits.length+1) := by
  obtain ⟨rep,rest,ha,hr,hm⟩ := hv
  have ht := rawFrames_tail_le h.assignments
  simp only [headCost,HeadInput.bits,List.length_append,Encoding.length_frame,hm]
  omega

theorem headsCost_le (heads : List HeadInput) (n : ℕ)
    (hv : ∀ h∈heads,Valid n h) :
    headsCost heads n ≤ 200*((headsBits heads).length+1) := by
  induction heads with
  | nil => simp [headsCost,headsBits]
  | cons h hs ih =>
      have hh := headCost_le h n (hv h (by simp))
      have ht := ih (fun x hx => hv x (by simp [hx]))
      simp only [headsCost,List.map_cons,List.sum_cons] at ht ⊢
      simp only [headsBits,List.map_cons,rawFrames,List.length_append,Encoding.length_frame]
      change (List.map (fun h => headCost h n + 2) hs).sum + 1 ≤
        200*((headsBits hs).length+1) at ht
      simp only [headsBits] at ht
      omega

theorem tupleCost_le (heads : List HeadInput) (n : ℕ)
    (hv : ∀ h∈heads,Valid n h) :
    tupleCost heads n ≤ 300*((headsBits heads).length+n+1) := by
  have hh := headsCost_le heads n hv
  unfold tupleCost
  omega

theorem scanCost_le (tuples : Tuples) (n : ℕ)
    (hv : ∀ hs∈tuples,∀ h∈hs,Valid n h) :
    scanCost tuples n ≤ 400*(n+1)*((tuplesBits tuples).length+1) := by
  induction tuples with
  | nil => simp [scanCost,tuplesBits,Encoding.encodeList]; omega
  | cons hs tuples ih =>
      have hh := tupleCost_le hs n (hv hs (by simp))
      have ht := ih (fun xs hx => hv xs (by simp [hx]))
      have hlen : (tuplesBits (hs::tuples)).length=
          2*(headsBits hs).length+2+(tuplesBits tuples).length := by
        simp [tuplesBits,Encoding.length_encodeList_cons]
      simp only [scanCost,List.map_cons,List.sum_cons] at ht ⊢
      rw [hlen]
      nlinarith [Nat.zero_le (n*(headsBits hs).length)]

theorem cost_le (width : List Bool) (tuples : Tuples)
    (hv : ∀ hs∈tuples,∀ h∈hs,Valid width.length h) :
    cost width tuples ≤ 500*(width.length+1)*((tuplesBits tuples).length+1) := by
  have hs := scanCost_le tuples width.length hv
  unfold cost
  nlinarith [Nat.zero_le (width.length*(tuplesBits tuples).length)]

theorem primitive_runsIn (regs : Fin 8 → Bool) (width : List Bool) (tuples : Tuples)
    (hv : ∀ heads∈tuples,∀ h∈heads,Valid width.length h) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program*(cost width tuples+1))
      (primitiveCfg program ((zeroStart regs width (tuplesBits tuples) []).withPC (some program.entry)))
      (primitiveCfg program ((state rf width [] [] [] []
        (MomentsAssembly.bucketsInput ((tuples.map (bucket width.length)).reverse))).withPC none)) := by
  obtain ⟨rf,he⟩ := command_eval regs width tuples hv
  exact ⟨rf,BitProgram.primitive_trace program (compiled_halt_trace he 0 8)⟩

end Representative
end SubexponentialSAT.SqrtLog.BucketTupleProgram

end OAI.Algorithms
