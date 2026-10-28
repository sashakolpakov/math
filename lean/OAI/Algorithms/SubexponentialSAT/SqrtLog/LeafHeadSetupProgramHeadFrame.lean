import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramStep

namespace OAI.Algorithms

/-! Outside the address and tuple accumulator, a complete head iteration can
only shorten stored words. Thus the persistent space bound does not compound
with the number of heads. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem preparedHead_nonoutput_length_le (a : Data) (rp : Fin 8 → Bool)
    (n N : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) (i : Fin 768)
    (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
    ((preparedHead a rp n N rows low W z).stacks i).length ≤ (a.stacks i).length := by
  let b := headResult a n rows low W z
  let c := countResult b
  let d := scatterResult c rp n (selectedHeads n rows low z)
  have hb : (b.stacks i).length ≤ (a.stacks i).length :=
    returned_nonoutput_length_le id (by decide) headInputs headOutputs a _ i
      (by simp [headOutputs,h650,h651])
  have hc : (c.stacks i).length ≤ (b.stacks i).length :=
    returned_nonoutput_length_le countRegs (by decide) countInputs countOutputs b _ i
      (by simp [countOutputs,h652])
  have hd : (d.stacks i).length ≤ (c.stacks i).length :=
    returned_nonoutput_length_le scatterRegs (by decide) scatterInputs scatterOutputs c _ i
      (by simp [scatterOutputs,h670])
  have he : ((factorResult d n N rows W z).stacks i).length ≤ (d.stacks i).length :=
    returned_nonoutput_length_le id (by decide) factorInputs factorOutputs d _ i
      (by simp [factorOutputs,h671])
  exact he.trans (hd.trans (hc.trans hb))

theorem headStepResult_nonoutput_length_le (a : Data) (rp : Fin 8 → Bool)
    (mb : State 16 288) (rt : Fin 10 → Bool) (n N W z : ℕ)
    (rows prior : List (List Bool)) (low : List Bool) (shifted : List (List (List Bool)))
    (i : Fin 768) (h649 : i≠649) (h660 : i≠660) :
    ((headStepResult a rp mb rt n N W z rows prior low shifted).stacks i).length ≤
      (a.stacks i).length := by
  let p := preparedHead a rp n N rows low W z
  let m := returned id (by decide) matrixInputs matrixOutputs p mb
  let bs := BucketTupleProgram.actualBuckets (a.stacks 141) shifted (selectedHeads n rows low z)
    n (selectedHeads n rows low z).length
  let q := tupleResult m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs
  by_cases hclean : i∈([650,651,652,669,670,671] : List (Fin 768))
  · simp [headStepResult,SubexponentialSAT.Subexp.TupleProgram.pushedState,clearMany_stacks,h649,hclean]
  have hp : (p.stacks i).length ≤ (a.stacks i).length := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hclean
    exact preparedHead_nonoutput_length_le a rp n N rows low W z i
      hclean.1 hclean.2.1 hclean.2.2.1 hclean.2.2.2.2.1 hclean.2.2.2.2.2
  have h669 : i≠669 := by intro he; subst i; simp at hclean
  have hm : (m.stacks i).length ≤ (p.stacks i).length :=
    returned_nonoutput_length_le id (by decide) matrixInputs matrixOutputs p mb i
      (by simp [matrixOutputs,h669])
  have hq : (q.stacks i).length ≤ (m.stacks i).length :=
    returned_nonoutput_length_le tupleRegs (by decide) tupleInputs tupleOutputs m _ i
      (by simp [tupleOutputs,h660])
  have heq : (headStepResult a rp mb rt n N W z rows prior low shifted).stacks i=q.stacks i := by
    simp [headStepResult,SubexponentialSAT.Subexp.TupleProgram.pushedState,clearMany_stacks,h649,hclean,q,m,p,bs]
  rw [heq]
  exact hq.trans (hm.trans hp)

theorem headStepResult_clean (a : Data) (rp : Fin 8 → Bool)
    (mb : State 16 288) (rt : Fin 10 → Bool) (n N W z : ℕ)
    (rows prior : List (List Bool)) (low : List Bool) (shifted : List (List (List Bool)))
    (i : Fin 768) (hi : i∈([650,651,652,669,670,671] : List (Fin 768))) :
    (headStepResult a rp mb rt n N W z rows prior low shifted).stacks i=[] := by
  have h649 : i≠649 := by intro he; subst i; simp at hi
  simp [headStepResult,SubexponentialSAT.Subexp.TupleProgram.pushedState,clearMany_stacks,h649,hi]


theorem headStepResult_address (a : Data) (rp : Fin 8 → Bool)
    (mb : State 16 288) (rt : Fin 10 → Bool) (n N W z : ℕ)
    (rows prior : List (List Bool)) (low : List Bool) (shifted : List (List (List Bool))) :
    (headStepResult a rp mb rt n N W z rows prior low shifted).stacks 649=true::a.stacks 649 := by
  let p := preparedHead a rp n N rows low W z
  let m := returned id (by decide) matrixInputs matrixOutputs p mb
  let bs := BucketTupleProgram.actualBuckets (a.stacks 141) shifted (selectedHeads n rows low z)
    n (selectedHeads n rows low z).length
  let q := tupleResult m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs
  have hp : p.stacks 649=a.stacks 649 := preparedHead_frame a rp n N rows low W z 649
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hm : m.stacks 649=p.stacks 649 := returned_frame id (by decide) matrixInputs matrixOutputs p mb
    649 (by decide) (by simp [matrixOutputs])
  have hq : q.stacks 649=m.stacks 649 := tupleResult_frame m rt prior _ _ bs 649 (by decide) (by decide)
  change (SubexponentialSAT.Subexp.TupleProgram.pushedState (649:Fin 768) (0:Fin 16) true
    (clearManyState [650,651,652,669,670,671] q)).stacks 649=true::a.stacks 649
  simp [clearMany_stacks,hq,hm,hp]

theorem headStepResult_tuples (a : Data) (rp : Fin 8 → Bool)
    (mb : State 16 288) (rt : Fin 10 → Bool) (n N W z : ℕ)
    (rows prior : List (List Bool)) (low : List Bool) (shifted : List (List (List Bool))) :
    (headStepResult a rp mb rt n N W z rows prior low shifted).stacks 660=
      ProgramEncoding.encodeRecords (BucketTupleProgram.Expand.nextRows prior (selectedMask n rows low z)
        (selectedContext n N rows z) (BucketTupleProgram.actualBuckets (a.stacks 141) shifted
          (selectedHeads n rows low z) n (selectedHeads n rows low z).length)) := by
  let p := preparedHead a rp n N rows low W z
  let m := returned id (by decide) matrixInputs matrixOutputs p mb
  let bs := BucketTupleProgram.actualBuckets (a.stacks 141) shifted (selectedHeads n rows low z)
    n (selectedHeads n rows low z).length
  simpa [headStepResult,SubexponentialSAT.Subexp.TupleProgram.pushedState,clearMany_stacks,p,m,bs] using
    tupleResult_value m rt prior (selectedMask n rows low z) (selectedContext n N rows z) bs

theorem headStepResult_wordBound (a : Data) (rp : Fin 8 → Bool)
    (mb : State 16 288) (rt : Fin 10 → Bool) (n N W z A : ℕ)
    (rows prior : List (List Bool)) (low : List Bool) (shifted : List (List (List Bool)))
    (ha : WordBound A a) (hz : z+1 ≤ A) (ha649 : a.stacks 649=unary z)
    (hsize : (ProgramEncoding.encodeRecords
      (BucketTupleProgram.Expand.nextRows prior (selectedMask n rows low z) (selectedContext n N rows z)
        (BucketTupleProgram.actualBuckets (a.stacks 141) shifted (selectedHeads n rows low z)
          n (selectedHeads n rows low z).length))).length ≤ A) :
    WordBound A (headStepResult a rp mb rt n N W z rows prior low shifted) := by
  intro i
  by_cases h649 : i=649
  · subst i
    rw [headStepResult_address,ha649]
    simpa [unary] using hz
  by_cases h660 : i=660
  · subst i
    rw [headStepResult_tuples]
    exact hsize
  exact (headStepResult_nonoutput_length_le a rp mb rt n N W z rows prior low shifted i h649 h660).trans
    (ha i)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
