import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopePreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeReachable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeAssignment

namespace OAI.Algorithms

/-! One explicit cap for all reachable assignment reference states, including
mutable moment dictionaries and parser streams. -/
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage MomentsAssembly MomentsProgram
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram
open MomentsAssembly.Relational

def memoryCap (s : HeadInputs) (input bucketBytes B d u J : ℕ) : ℕ :=
  spaceBudget s input bucketBytes J+s.n+
    dictionaryByteEnvelope B d (s.n+u+J)
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) u J)

def assignmentCap (s : HeadInputs) (input bucketBytes B d u J : ℕ) : ℕ :=
  524288*memoryCap s input bucketBytes B d u J+1

theorem preparation_reachable {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (input bucketBytes B d u J : ℕ)
    (hb : WordBound input a) (hJ : a.stacks 243=List.replicate J true)
    (hstream : (bucketsInput pr.bucketInputs).length ≤ bucketBytes) :
    Reachable.BucketFrames B d (Finset.univ : Finset (Fin s.n)) u J
      (WordCap (memoryCap s input bucketBytes B d u J))
      b.stacks pr.supports pr.bucketInputs := by
  have hbase := preparation_wordCap pr ha input bucketBytes J hb hJ hstream
  have hsupport : (rawFrames (pr.supports.map Squarefree.encodeMask)).length=
      SupportProgram.count s.n J*(2*s.n+1) := by
    rw [LeafSupportInputProgram.supportFrames_length,(pr.support_cap J hJ).2]
  apply reachable_wordCap
  · exact hbase.mono (by unfold memoryCap; omega)
  · exact hstream.trans (by unfold memoryCap spaceBudget; omega)
  · rw [hsupport]; unfold memoryCap spaceBudget; omega
  · unfold memoryCap; omega
  · unfold memoryCap; omega

def AssignmentStorage {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (degree : List Bool) (A : ℕ) (high : Fin 768 → List Bool) : Prop :=
  let base := FactorLoop.preparedAssignment q degree (FactorLoop.maskedHigh high) [] []
  WordCap A base ∧ WordBound A (Incidence.staged (FactorReady.baseData base)) ∧
    FactorLoop.byteBound n (SubexpLiftRing.baseWidth 3 q.p.t) d q.u q.J ≤ A

/-- Only the equality of the actual prepared arithmetic core to the factor
environment is required; its size comes from the native preparation above. -/
theorem preparation_assignment_storage {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (input bucketBytes : ℕ)
    (hb : WordBound input a) {r Q d : ℕ} (q : Factor.Spec r Q s.n d)
    (degree : List Bool) (hJ : a.stacks 243=List.replicate q.J true)
    (hstream : (bucketsInput pr.bucketInputs).length ≤ bucketBytes)
    (hcore : ∀ i : Fin 56,b.stacks (corePorts i)=
      Product.tapes (emptyCore (FactorLoop.assignmentEnvironment q degree)) i) :
    Reachable.BucketFrames (SubexpLiftRing.baseWidth 3 q.p.t) d
      (Finset.univ : Finset (Fin s.n)) q.u q.J
      (AssignmentStorage q degree
        (assignmentCap s input bucketBytes (SubexpLiftRing.baseWidth 3 q.p.t) d q.u q.J))
      b.stacks pr.supports pr.bucketInputs := by
  let C := memoryCap s input bucketBytes (SubexpLiftRing.baseWidth 3 q.p.t) d q.u q.J
  have hbase : WordCap C b.stacks := (preparation_wordCap pr ha input bucketBytes q.J hb hJ hstream).mono
    (by dsimp [C,memoryCap]; omega)
  have hc : ∀ i,(Product.tapes (emptyCore (FactorLoop.assignmentEnvironment q degree)) i).length ≤ C := by
    intro i
    rw [←hcore i]
    exact hbase _
  refine reachable_mono (Finset.univ : Finset (Fin s.n)) q.u q.J (WordCap C)
    (AssignmentStorage q degree
      (assignmentCap s input bucketBytes (SubexpLiftRing.baseWidth 3 q.p.t) d q.u q.J))
    b.stacks pr.supports pr.bucketInputs
    (preparation_reachable pr ha input bucketBytes (SubexpLiftRing.baseWidth 3 q.p.t) d q.u q.J hb hJ hstream) ?_
  intro high hh
  have hp := preparedAssignment_bound q degree (FactorLoop.maskedHigh high) C hh.masked hc
  have hstage := incidence_staged_bound
    (FactorReady.baseData (FactorLoop.preparedAssignment q degree (FactorLoop.maskedHigh high) [] [])) C hp
  refine ⟨hp.mono (by dsimp [C,assignmentCap]; omega),hstage,?_⟩
  change dictionaryByteEnvelope (SubexpLiftRing.baseWidth 3 q.p.t) d (s.n+q.u+q.J)
    (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) q.u q.J) ≤ _
  dsimp [assignmentCap,memoryCap]
  omega

end SubexponentialSAT.SqrtLog.NodeEnvelope

end OAI.Algorithms
