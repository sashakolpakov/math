import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativePackingBounds

namespace OAI.Algorithms

/-! Explicit scalar envelope for the actual two-address packing call. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes LayoutProgram

/-- Both represented alphabets are charged at their actual cardinality. -/
def addressSize (D M r Q : ℕ) : ℕ :=
  D+1+r^(2*Q)+Q*r+M*(Q*r)+
    (1+(2*(Q*r)+2)*r^Q)+(1+(16*M+24)*D)+1

def addressScalarSize (D M r Q : ℕ) : ℕ :=
  D+M+Q*r+r^Q+r^(2*Q)+1

theorem addressSize_polynomial (D M r Q : ℕ) :
    addressSize D M r Q ≤ 64*(addressScalarSize D M r Q)^2 := by
  let S := addressScalarSize D M r Q
  have hS : 1 ≤ S := by dsimp [S,addressScalarSize]; omega
  have hD : D ≤ S := by dsimp [S,addressScalarSize]; omega
  have hM : M ≤ S := by dsimp [S,addressScalarSize]; omega
  have hW : Q*r ≤ S := by dsimp [S,addressScalarSize]; omega
  have hA : r^Q ≤ S := by dsimp [S,addressScalarSize]; omega
  have hN : r^(2*Q) ≤ S := by dsimp [S,addressScalarSize]; omega
  have h2 : S ≤ S^2 := PackingBudgetArithmetic.le_power hS (by decide)
  have h12 : 1 ≤ S^2 := hS.trans h2
  change addressSize D M r Q ≤ 64*S^2
  unfold addressSize
  calc
    _ ≤ S+1+S+S+S*S+(1+(2*S+2)*S)+(1+(16*S+24)*S)+1 := by gcongr
    _ ≤ 64*S^2 := by ring_nf; omega

variable {D r Q : ℕ}

theorem address_plan_stream_le (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    (ProgramEncoding.encodeRecords ((labelPlans words address).map PackingVertexLabels.planPayload)).length
      ≤ 1+(16*words.length+24)*D := by
  have hp : ∀ plan∈labelPlans words address,
      (PackingVertexLabels.planBytes plan).length ≤ 4*words.length+5 := by
    intro plan hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    have h1 := (address i).1.isLt
    have h2 := (address i).2.isLt
    simp only [PackingVertexLabels.planBytes,GatherProgram.encoded_plan_length,
      List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have h := ProgramEncoding.encodeRecords_length_le
    ((labelPlans words address).map PackingVertexLabels.planPayload) (8*words.length+11) (by
      intro p hm
      obtain ⟨plan,hplan,rfl⟩ := List.mem_map.mp hm
      have h := hp plan hplan
      simpa [PackingVertexLabels.planPayload,PackingVertexLabels.planBytes,
        Encoding.length_frame] using (show 2*(PackingVertexLabels.planBytes plan).length+1 ≤ 8*words.length+11 by omega))
  simp only [List.length_map,labelPlans,List.length_finRange] at h
  unfold labelPlans
  calc
    _ ≤ 1+(2*(8*words.length+11)+2)*D := h
    _ = 1+(16*words.length+24)*D := by ring

theorem address_sourceSize_le (hr : 0 < r) (hQ : 0 < Q)
    (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    sourceSize (NativePacking.addressSpec hr hQ words address) ≤ addressSize D words.length r Q := by
  have hw : ∀ row∈words.map ReadPlan.encodeWord, row.length ≤ Q*r := by
    intro row hm
    obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hm
    simp [ReadPlan.encodeWord_length,ReadPlan.wordWidth]
  have hf := PairScoreBounds.volume_le (words.map ReadPlan.encodeWord) (Q*r) hw
  have hf' : (words.map ReadPlan.encodeWord).flatten.length ≤ words.length*(Q*r) := by
    simpa [List.length_flatten,PairScoreBounds.volume] using hf
  have ha := ProgramEncoding.encodeRecords_length_le (AssignmentAlphabetSemantics.wordBytes r Q)
    (Q*r) (fun row hm => (AssignmentAlphabetSemantics.wordBytes_width hr row hm).le)
  rw [AssignmentAlphabetSemantics.wordBytes_length] at ha
  have ht := PackingCanonicalSpec.types_length hr hQ 1
  simp only [blockSize,Nat.reduceAdd] at ht
  rw [Nat.mul_comm Q 2] at ht
  have hp := address_plan_stream_le words address
  unfold sourceSize addressSize
  dsimp only [NativePacking.addressSpec,NativeFrontend.Params.planStream]
  simp only [List.length_replicate,ht]
  omega

/-- No scope-dependent specification is used in this bound. -/
theorem address_budget_le (hr : 0 < r) (hQ : 0 < Q)
    (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    NativePacking.budget (NativePacking.addressSpec hr hQ words address) ≤
      81000000*(addressSize D words.length r Q)^12 :=
  (budget_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (address_sourceSize_le hr hQ words address) 12))

/-- Metadata emitted on native packing port32. -/
theorem metadata_output_bytes_le {U : Type*} [DecidableEq U]
    (s : NativePacking.Spec U) : s.suffix.metadata.length ≤ 34*sourceSize s^4 :=
  (metadata_length_le s).trans (PackingBudgetArithmetic.metadata_le _ _ _
    (sourceSize_pos s) (dimension_le s) (type_stream_le s))

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
