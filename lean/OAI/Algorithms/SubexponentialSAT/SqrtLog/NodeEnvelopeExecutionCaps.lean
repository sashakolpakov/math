import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeState

namespace OAI.Algorithms

/-! The actual prepared streams supply all size arguments used by the dense
execution theorem at the same canonical assignment-storage cap. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage MomentsAssembly
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram

theorem rawFrames_count_le (xs : List (List Bool)) : xs.length ≤ (rawFrames xs).length := by
  induction xs with
  | nil => simp [rawFrames]
  | cons x xs ih =>
    simp only [rawFrames,List.length_cons,List.length_append,Encoding.length_frame]
    omega

theorem bucketSize_self (v : BucketInput) (A : ℕ) (hv : v.bits.length ≤ A) :
    BucketSize A A A v := by
  have hhead : (rawFrames (v.heads.map HeadInput.bits)).length ≤ A := by
    simp only [BucketInput.bits,List.length_append,Encoding.length_frame] at hv
    omega
  apply bucketSize_of_bits v A A A hv
  · have hc : v.heads.length ≤ (rawFrames (v.heads.map HeadInput.bits)).length := by
      simpa only [List.length_map] using rawFrames_count_le (v.heads.map HeadInput.bits)
    exact hc.trans hhead
  · intro h hh
    have hbits := (rawFrames_member_length_le (v.heads.map HeadInput.bits) h.bits
      (List.mem_map.mpr ⟨h,hh,rfl⟩)).trans hhead
    have hassign : (rawFrames h.assignments).length ≤ A := by
      simp only [HeadInput.bits,List.length_append,Encoding.length_frame] at hbits
      omega
    exact (rawFrames_count_le h.assignments).trans hassign

theorem preparation_execution_caps {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (input bucketBytes B d u J : ℕ)
    (hb : WordBound input a) (hJ : a.stacks 243=List.replicate J true)
    (hstream : (bucketsInput pr.bucketInputs).length ≤ bucketBytes) :
    let A := assignmentCap s input bucketBytes B d u J
    (∀ v∈pr.bucketInputs,BucketSize A A A v) ∧
    (b.stacks 169).length ≤ A ∧
    (∀ i∈Node.cleanupPorts,(b.stacks i).length ≤ A) ∧
    dictionaryByteEnvelope B d (s.n+u+J)
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J) ≤ A ∧
    (bucketsInput pr.bucketInputs).length ≤ A ∧ WordCap A b.stacks := by
  dsimp only
  let A := assignmentCap s input bucketBytes B d u J
  have hspace : spaceBudget s input bucketBytes J ≤ A := by
    dsimp [A,assignmentCap,memoryCap]
    omega
  have hbytes : bucketBytes ≤ A := by
    dsimp [A,assignmentCap,memoryCap,spaceBudget]
    omega
  have hw : WordCap A b.stacks :=
    (preparation_wordCap pr ha input bucketBytes J hb hJ hstream).mono hspace
  refine ⟨?_,hw 169,fun i _=>hw i,?_,hstream.trans hbytes,hw⟩
  · intro v hv
    apply bucketSize_self v A
    exact (rawFrames_member_length_le (pr.bucketInputs.map BucketInput.bits) v.bits
      (List.mem_map.mpr ⟨v,hv,rfl⟩)).trans (hstream.trans hbytes)
  · dsimp [A,assignmentCap,memoryCap]
    omega

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms
