import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPayload
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramTuples

namespace OAI.Algorithms

/-! Paid final moments serialization and cleanup after the head loop. Output
bytes are bounded from the actual serializer trace, retaining every bucket. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open BucketTupleProgram

 theorem final_payload_bound (width : List Bool) (tuples : Representative.Tuples) (A : ℕ)
    (hw : width.length ≤ A) (ht : (Representative.tuplesBits tuples).length ≤ A)
    (hv : ∀ heads∈tuples,∀ h∈heads,Representative.Valid width.length h) :
    (MomentsAssembly.bucketsInput ((tuples.map (Representative.bucket width.length)).reverse)).length ≤
      502*(A+1)^2 := by
  obtain ⟨rf,hrun⟩ := Representative.program_runsIn (fun _=>false) width tuples hv
  have hi : WordBound A (Representative.zeroStart (fun _=>false) width (Representative.tuplesBits tuples) []) := by
    intro i
    fin_cases i <;> simp only [Representative.zeroStart,Matrix.cons_val_zero',Matrix.cons_val_succ',
      List.length_nil] <;> first | exact hw | exact ht | omega
  have ho := runsIn_wordBound hrun hi 8
  have hc := Representative.cost_le width tuples hv
  have hc' : Representative.cost width tuples ≤ 500*(A+1)^2 := by
    calc
      _ ≤ 500*(A+1)*(A+1) := hc.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 1)) (Nat.add_le_add_right ht 1))
      _ = _ := by ring
  change (MomentsAssembly.bucketsInput ((tuples.map (Representative.bucket width.length)).reverse)).length ≤
    A+(Representative.cost width tuples+1) at ho
  nlinarith only [ho,hc',Nat.zero_le A,Nat.zero_le (A^2)]

 theorem final_stage_bound (a : Data) (regs : Fin 8 → Bool) (width : List Bool)
    (tuples : Representative.Tuples) (A : ℕ) (ha : WordBound A a)
    (hw : width.length ≤ A) (ht : (Representative.tuplesBits tuples).length ≤ A)
    (hv : ∀ heads∈tuples,∀ h∈heads,Representative.Valid width.length h) :
    WordBound (502*(A+1)^2) (finalResult a regs width tuples) ∧
      finalCost a regs width tuples ≤ 100000*(A+1)^2 := by
  have hsmall : A ≤ 502*(A+1)^2 := by nlinarith only [Nat.zero_le A,Nat.zero_le (A^2)]
  have hb := final_payload_bound width tuples A hw ht hv
  have hl : WordBound (502*(A+1)^2) (Representative.state regs width [] [] [] []
      (MomentsAssembly.bucketsInput ((tuples.map (Representative.bucket width.length)).reverse))) := by
    intro i
    fin_cases i <;> simp only [Representative.state,Matrix.cons_val_zero',Matrix.cons_val_succ',
      List.length_nil,List.length_replicate] <;> first | exact hb | exact hw.trans hsmall | omega
  have ha' := wordBound_mono ha hsmall
  refine ⟨returned_wordBound finalRegs (by decide) finalInputs finalOutputs a _ _
    finalInputs_protected finalOutputs_protected (by decide) (by decide) ha' hl,?_⟩
  have hs := stageCost_linear finalRegs (by decide) finalInputs finalOutputs a _
    (Representative.cost width tuples+1) (502*(A+1)^2)
    finalInputs_protected finalOutputs_protected (by decide) (by decide) ha' hl
  change finalCost a regs width tuples ≤ _ at hs
  norm_num [finalInputs,finalOutputs] at hs
  have hc := Representative.cost_le width tuples hv
  have hc' : Representative.cost width tuples ≤ 500*(A+1)^2 := by
    calc
      _ ≤ 500*(A+1)*(A+1) := hc.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw 1)) (Nat.add_le_add_right ht 1))
      _ = _ := by ring
  have h1 : 1 ≤ (A+1)^2 := one_le_pow₀ (by omega)
  nlinarith only [hs,hc',h1]

 theorem final_cleanup_bound (ports : List (Fin 768)) (a : Data) (regs : Fin 8 → Bool)
    (width : List Bool) (tuples : Representative.Tuples) (A : ℕ) (ha : WordBound A a)
    (hw : width.length ≤ A) (ht : (Representative.tuplesBits tuples).length ≤ A)
    (hv : ∀ heads∈tuples,∀ h∈heads,Representative.Valid width.length h) :
    finalCost a regs width tuples+clearManyCost ports (finalResult a regs width tuples) ≤
      (100000+1007*ports.length)*(A+1)^2 := by
  obtain ⟨hb,hc⟩ := final_stage_bound a regs width tuples A ha hw ht hv
  have hclean := clearManyCost_le ports (finalResult a regs width tuples) (502*(A+1)^2) hb
  have h1 : 1 ≤ (A+1)^2 := one_le_pow₀ (by omega)
  nlinarith only [hc,hclean,h1]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
