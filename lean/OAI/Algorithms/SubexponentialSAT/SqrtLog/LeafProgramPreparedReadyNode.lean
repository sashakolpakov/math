import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyHead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadySource

namespace OAI.Algorithms

/-! Actual head preparation supplies the layout half of the source contract;
only retained arithmetic words are taken from the parked query state. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open NodeNative LeafHeadSetupProgram LayoutProgram
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

structure SourceStatic {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a : NodeNative.Data) : Prop where
  inverses : a.stacks 713=(List.ofFn (fun i=>RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i=>RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 715=(List.ofFn (fun i=>
    (List.ofFn (fun j=>RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 717=p.ringWidth
  rowWidth : a.stacks 716=p.rowWidth
  zero : a.stacks 280=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 207=RingProgram.flat p.ops.oneRun.1
  minusOne : a.stacks 211=RingProgram.flat p.minusOne
  inverseDenominator : a.stacks 728=RingProgram.flat p.invDenom

variable {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : NodeNative.Ready s a)

include pr ha

 theorem preparation_source_masters {d : ℕ} (p : SourceBank.Parameters s.r s.Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType s.r s.Q 1))
    (hm : SourceStatic p a)
    (hR : p.R=s.R) (hwords : p.hwords=pr.head.words)
    (hwidth : p.width=s.width) (hpower : p.power=s.power) (hoffset : p.aWord=s.height)
    (hps : ps=s.plans)
    (hmeta : s.metadata=SelectorProgram.rawRecords
      (PackingMetadata.records P (fun v=>List.replicate v.val true) CollisionProgram.encodeType)) :
    SourceMasters p ps P (FactorReady.baseData b.stacks) := by
  obtain ⟨hn,hr,hq,hw,hmet,hplans,horder,hheight,hwid⟩ := loaded_layout pr ha
  refine ⟨hr,hq,hw,?_,?_,hwid.trans hwidth.symm,?_,?_,?_,?_,hmet.trans hmeta,?_,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [SourceBank.Parameters.saved,LayoutProgramScalar.FromCounts.unsignedSaved,hwords]
      using generated_positive pr ha
  · simpa [SourceBank.Parameters.saved,LayoutProgramScalar.FromCounts.unsignedSaved,hR,hwidth]
      using generated_negative pr ha
  · simpa only [hpower] using generated_power pr ha
  · simp [hpower,Native.Inputs.power]
  · simpa only [hR] using horder
  · exact hheight.trans hoffset.symm
  · simpa only [hps] using hplans
  all_goals first
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.inverses
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.negatives
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.differences
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.ringWidth
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.rowWidth
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.zero
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.one
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.minusOne
    | exact (pr.frame _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.inverseDenominator

omit ha in
 theorem preparation_node : b.stacks 78=a.stacks 78 := by
  rw [pr.support_frame 78 (by decide),pr.cached_words,
    LeafNodeCacheProgram.cache_frame _ 78 (by decide)]
  change pr.headEnd.stacks 78=a.stacks 78
  rw [pr.head.frame 78 (by decide),pr.loaded_words]
  exact LayoutMasters.loaded_frame (LayoutMasters.project a) 78 (by decide)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
