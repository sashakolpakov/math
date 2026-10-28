import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyContexts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyBounds

namespace OAI.Algorithms

/-! Every actual nested moment-loop assignment receives the fully constructed
physical factor contract. Storage is the separately proved reachable bound. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open MomentsAssembly MomentsProgram MomentsAssembly.Relational
open NodeNative LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem preparation_assignment_frames {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) {d A : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (hfacts : NodeFacts q b.stacks)
    (hzero : b.stacks 190=RingProgram.flat q.p.ops.zeroRun.1)
    (hRQ : q.p.R+1 ≤ s.Q)
    (hstorage : Reachable.BucketFrames (baseWidth 3 q.p.t) d Finset.univ q.u q.J
      (NodeEnvelope.AssignmentStorage q (List.replicate d true) A)
      b.stacks pr.supports pr.bucketInputs) :
    Reachable.BucketFrames (baseWidth 3 q.p.t) d Finset.univ q.u q.J
      (fun high=>FactorLoop.AssignmentFrame q (List.replicate d true)
        (FactorResource.sourceCap q A A A) A A A LeafStatisticsProgram.Arity.decoded
        q.p.ops.zeroRun.1 q.p.ops.oneRun.1 (b.stacks 702) (b.stacks 703) (FactorLoop.maskedHigh high))
      b.stacks pr.supports pr.bucketInputs := by
  intro seed hseed source hsource bucket hb tail htail seed' hseed' source' hsource' support hs tail'
    htail' head hh headTail hheadTail assignmentTail hat x hx
  let cur := Function.update (Function.update
    (headHigh (supportHigh (supportStream (bucketHigh (bucketStream b.stacks
      (Product.bytes seed) source) bucket tail) (Product.bytes seed') source')
      (Squarefree.encodeMask support) tail') head headTail) 160 assignmentTail) 174 x
  have hframe : MomentFrame b.stacks cur := reachable_master_frame Finset.univ q.u q.J
    b.stacks pr.supports pr.bucketInputs seed hseed source hsource bucket hb tail htail
    seed' hseed' source' hsource' support hs tail' htail' head hh headTail hheadTail assignmentTail hat x hx
  have hstore : NodeEnvelope.AssignmentStorage q (List.replicate d true) A cur :=
    hstorage seed hseed source hsource bucket hb tail htail seed' hseed' source' hsource'
      support hs tail' htail' head hh headTail hheadTail assignmentTail hat x hx
  have hshape := reachable_shapes Finset.univ q.u q.J b.stacks pr.supports pr.bucketInputs
    (preparation_bucket_shapes pr) seed hseed source hsource bucket hb tail htail
    seed' hseed' source' hsource' support hs tail' htail' head hh headTail hheadTail assignmentTail hat x hx
  have hnf : NodeFacts q cur := hfacts.frame hframe
  have hctx : cur 175=head.context := by
    simp [cur,headHigh,headHigh1,headHigh2,headHigh3]
  have hsup : (cur 168).length=s.n := by
    simp [cur,headHigh,headHigh1,headHigh2,headHigh3,supportHigh,Squarefree.encodeMask]
  have hN : b.stacks 129=List.replicate s.N true :=
    (pr.loaded_word 1).trans ha.heads.factors
  have hNA : s.N ≤ A := by
    have ht := hstore.1 129
    change (assignmentBase q (List.replicate d true) cur 129).length ≤ A at ht
    rw [assignment_fixed q _ cur 129 (by decide) (by decide) (by decide),hframe 129 (by decide),hN,List.length_replicate] at ht
    exact ht
  have hlen : (cur 175).length ≤ A := by
    have ht := hstore.1 175
    change (assignmentBase q (List.replicate d true) cur 175).length ≤ A at ht
    rwa [assignment_fixed q _ cur 175 (by decide) (by decide) (by decide)] at ht
  have hc := preparation_head_contexts pr bucket hb head hh
  have hids : cur 175=ProgramEncoding.encodeRecords
      (FactorLoop.records (LeafStatisticsProgram.Arity.decoded (cur 175))) := by
    simpa only [hctx] using hc.1
  have hid : ∀ f∈LeafStatisticsProgram.Arity.decoded (cur 175),f ≤ A := by
    intro f hm
    rw [hctx] at hm
    exact (hc.2 f hm).le.trans hNA
  have hbounds := source_bounds hnf hstore hRQ
  have hAS : A ≤ FactorResource.sourceCap q A A A :=
    (FactorResource.sourceCap_limits q A A A).base_le_source
  exact assignment_frame hnf hstore hshape.1 hshape.2.2 hshape.2.1 hsup
    LeafStatisticsProgram.Arity.decoded hids hid hlen
    ((hframe 190 (by decide)).trans hzero) (b.stacks 702) (b.stacks 703)
    (hframe 702 (by decide)) (hframe 703 (by decide)) hAS
    (hbounds.1.trans hAS) (hbounds.2.1.trans hAS)
    (fun v=>⟨(hbounds.2.2.1 v).1.trans hAS,(hbounds.2.2.1 v).2.1.trans hAS,
      (hbounds.2.2.1 v).2.2.trans hAS⟩) (hbounds.2.2.2.trans hAS)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
