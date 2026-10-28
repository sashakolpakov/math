import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyMoments
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeState

namespace OAI.Algorithms

/-! A pure byte-and-shape join for the checked assignment executor. Its
engine is constructed from the actual setup, not supplied as a callback. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open MomentsAssembly MomentsProgram SubexpSetupStorage PerturbationAssembly
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem assignment_frame {r Q n d S A : ℕ} {q : Factor.Spec r Q n d}
    {high : Fin 768 → List Bool} (h : NodeFacts q high)
    (hs : NodeEnvelope.AssignmentStorage q (List.replicate d true) A high)
    (hx : (high 174).length=n) (hm : (high 178).length=n)
    (hb : (high 177).length=n) (hu : (high 168).length=n)
    (headIds : List Bool → List ℕ)
    (hids : high 175=ProgramEncoding.encodeRecords (FactorLoop.records (headIds (high 175))))
    (hid : ∀ id∈headIds (high 175),id ≤ A) (ht : (high 175).length ≤ A)
    (hzero : high 190=RingProgram.flat q.p.ops.zeroRun.1)
    (metadata702 metadata703 : List Bool) (h702 : high 702=metadata702) (h703 : high 703=metadata703)
    (hAS : A ≤ S) (harray : (q.p.R+1)*(d*baseWidth 3 q.p.t) ≤ S)
    (hcount : q.p.R+1 ≤ S)
    (hmeta : ∀ x,SourceBank.MetadataBound (PackingMetadata.value q.packing CollisionProgram.encodeType x) S)
    (hinc : q.ps.length ≤ S) :
    FactorLoop.AssignmentFrame q (List.replicate d true) S A A A headIds
      q.p.ops.zeroRun.1 q.p.ops.oneRun.1 metadata702 metadata703 (FactorLoop.maskedHigh high) := by
  have hf := FactorLoop.masked_at high
  have hin := h.input hx hs.1 hs.2.1 hAS harray hcount hmeta hinc
  constructor
  · intro i hi
    have hc : blankPort i ∧ ¬FactorLoop.collectorTape i := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (hf i hc.2).trans (h.clean i hc.1)
  · rw [hf 174 (by decide),hf 178 (by decide),hx,hm]
  · rw [hf 174 (by decide),hf 177 (by decide),hx,hb]
  · rw [hf 174 (by decide),hf 168 (by decide),hx,hu]
  · rw [hf 174 (by decide),hx]
  · simpa only [hf 175 (by decide)] using hids
  · simpa only [hf 175 (by decide)] using hid
  · simpa only [hf 175 (by decide)] using ht
  · exact (hf 69 (by decide)).trans h.one
  · exact (hf 190 (by decide)).trans hzero
  · exact (hf 207 (by decide)).trans h.source.one
  · exact (hf 702 (by decide)).trans h702
  · exact (hf 703 (by decide)).trans h703
  · exact hin
  · exact hs.2.2

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
