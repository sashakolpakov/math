import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyFacts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeConstants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramTape

namespace OAI.Algorithms

/-! Exact node preparation turns retained physical masters into the fixed
factor facts. Generated layout rows and cleared workspace come from the
actual preparation, rather than a caller-supplied readiness predicate. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open NodeNative LeafHeadSetupProgram LayoutProgram MomentsProgram
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

structure FactorStatic {s : HeadInputs} {d : ℕ} (q : Factor.Spec s.r s.Q s.n d)
    (a : NodeNative.Data) : Prop where
  source : SourceStatic q.p a
  modulus : a.stacks 194=q.p.modulus.bits
  width : a.stacks 202=q.width
  scalarZero : a.stacks 203=q.p.cache.zero.val
  table : a.stacks 201=RingTriple.tableEncoding (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache)
  degree : a.stacks 204=List.replicate d true
  theta : a.stacks 78=RingProgram.flat q.theta
  target : a.stacks 243=List.replicate q.J true
  highLength : (a.stacks 703).length=s.n
  rows : a.stacks 701=Encoding.encodeList id q.rawRows
  clauses : a.stacks 700=Encoding.encodeList id q.clauses
  count : a.stacks 704=List.replicate q.rawRows.length true
  mark : a.stacks 705=Encoding.encodeNat q.mark
  flag : a.stacks 706=[q.marked]
  hashWidth : (a.stacks 708).length=q.bitWidth
  hashModulus : BinaryArithmetic.toNat (a.stacks 707)=q.clauses.length
  code : a.stacks 281=RingProgram.flat q.code

 theorem preparation_facts {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) {d : ℕ} (q : Factor.Spec s.r s.Q s.n d)
    (hm : FactorStatic q a)
    (hR : q.p.R=s.R) (hwords : q.p.hwords=pr.head.words)
    (hwidth : q.p.width=s.width) (hpower : q.p.power=s.power) (hoffset : q.p.aWord=s.height)
    (hps : q.ps=s.plans)
    (hmeta : s.metadata=SelectorProgram.rawRecords
      (PackingMetadata.records q.packing (fun v=>List.replicate v.val true) CollisionProgram.encodeType))
    (hone : q.one=originEntries q.p.ops.oneRun.1) (hminus : q.minus=q.p.minusOne) :
    NodeFacts q b.stacks := by
  have hs := preparation_source_masters pr ha q.p q.ps q.packing hm.source
    hR hwords hwidth hpower hoffset hps hmeta
  have hf := pr.frame
  refine ⟨hs,preparation_blank pr ha,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.modulus
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.width
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.scalarZero
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.table
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.degree
  · exact (preparation_node pr).trans hm.theta
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.target
  · exact (loaded_layout pr ha).1
  · rw [hf _ (by rw [Node.mem_cleanup]; norm_num)]; exact hm.highLength
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.rows
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.clauses
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.count
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.mark
  · exact (hf _ (by rw [Node.mem_cleanup]; norm_num)).trans hm.flag
  · rw [hf _ (by rw [Node.mem_cleanup]; norm_num)]; exact hm.hashWidth
  · rw [hf _ (by rw [Node.mem_cleanup]; norm_num)]; exact hm.hashModulus
  · rw [hone]; exact (pr.one_entries ha q.p.ops.oneRun.1 hm.source.one).1
  · rw [hminus]; exact (pr.direct_master ha (211,76) (by decide) (by decide)).trans hm.source.minusOne
  · exact ((pr.direct_master ha (281,143) (by decide) (by decide)).trans hm.code).trans
      (IdempotentApplyProgram.coefficient_tape q.code)
  · have ht := (pr.direct_word ha (128,88) (by decide)).trans ha.heads.ambient
    simp only [ht, unary, List.length_replicate]

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
