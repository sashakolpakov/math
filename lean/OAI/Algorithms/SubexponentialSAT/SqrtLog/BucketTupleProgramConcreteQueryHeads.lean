import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteMerge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryPlan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramArity

namespace OAI.Algorithms

/-! The typed heads are read directly from the actual produced word rows.
No relation to real-valued packing weights is needed. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open SubexponentialSAT.MulticolorTypes PackingCallerProgram LeafProgram.NodeConcrete

variable (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) (t : Fin p.Q)

def queryFreeHead : {v : Fin p.n // v∉planHigh p} → Fin p.r :=
  fun v=>planHead p a tail t v.val

theorem query_low_get (hmask : p.mask.length=p.n) (v : Fin p.n) :
    (p.mask.map Bool.not).getD v.val false=decide (v∉planHigh p) := by
  have hv : v.val < p.mask.length := by rw [hmask]; exact v.isLt
  rw [List.getD_eq_getElem _ _ (by simpa using hv),List.getElem_map]
  have he := planHigh_mask p v
  rw [List.getD_eq_getElem _ _ hv] at he
  rw [he]
  simp

theorem query_head_predicate (hmask : p.mask.length=p.n) (g : Fin p.r) (v : Fin p.n) :
    HeadIdentifierProgram.predicate (ProducedQueryRank.rows p a tail)
      (p.mask.map Bool.not) (t.val*p.r+g.val) v.val=
      (decide (v∉planHigh p) && decide (planHead p a tail t v=g)) := by
  unfold HeadIdentifierProgram.predicate
  rw [ProducedQueryRank.head_row,HeadIdentifierProgram.encodeWord_getD,query_low_get p hmask]
  rfl

theorem query_ids_spec (hmask : p.mask.length=p.n) (g : Fin p.r) (v : Fin p.n) :
    v.val∈LeafHeadSetupProgram.selectedHeads p.n (ProducedQueryRank.rows p a tail)
      (p.mask.map Bool.not) (t.val*p.r+g.val) ↔
      ∃ hv : v∉planHigh p,queryFreeHead p a tail t ⟨v,hv⟩=g := by
  simp only [LeafHeadSetupProgram.selectedHeads,HeadIdentifierProgram.chosenIds,
    List.mem_filter,List.mem_range,v.isLt,true_and]
  rw [query_head_predicate p a tail t hmask]
  simp only [Bool.and_eq_true,decide_eq_true_eq,queryFreeHead]
  constructor
  · rintro ⟨hv,hg⟩; exact ⟨hv,hg⟩
  · rintro ⟨hv,hg⟩; exact ⟨hv,hg⟩

theorem query_factor_row (f : Fin p.factors) :
    (ProducedQueryRank.rows p a tail).getD (p.n+f.val) []=
      SubexponentialSAT.Subexp.ReadPlan.encodeWord (ProducedQueryRank.words p a tail (.inr f)) := by
  have hf : p.n+f.val < (p.words a tail).length := by rw [p.words_length]; omega
  unfold ProducedQueryRank.rows
  rw [List.getD_eq_getElem _ _ (by simpa using hf),List.getElem_map]
  rfl

theorem query_factor_ids (g : Fin p.r) :
    LeafHeadFactorsProgram.chosenIds
      (LeafHeadFactorsProgram.predicate (ProducedQueryRank.rows p a tail) p.n (t.val*p.r+g.val))
      p.factors = (List.range p.factors).filter (fun f=>decide (planColor p a tail t f=g)) := by
  unfold LeafHeadFactorsProgram.chosenIds
  apply List.filter_congr
  intro f hf
  have hlt : f < p.factors := List.mem_range.mp hf
  unfold LeafHeadFactorsProgram.predicate
  rw [query_factor_row p a tail ⟨f,hlt⟩,HeadIdentifierProgram.encodeWord_getD]
  simp only [planColor,dite_eq_left hlt]

theorem records_encode_nat (ids : List ℕ) :
    ProgramEncoding.encodeRecords (ids.map SubexponentialSAT.Encoding.encodeNat)=
      SubexponentialSAT.Encoding.encodeList SubexponentialSAT.Encoding.encodeNat ids := by
  induction ids with
  | nil => rfl
  | cons x xs ih => simpa only [List.map_cons,ProgramEncoding.encodeRecords,id_eq,
      SubexponentialSAT.Encoding.encodeList] using congrArg (fun ys=>true::(SubexponentialSAT.Encoding.frame
        (SubexponentialSAT.Encoding.encodeNat x)++ys)) ih

theorem query_context_ids (g : Fin p.r) :
    LeafStatisticsProgram.Arity.decoded
      (LeafHeadSetupProgram.selectedContext p.n p.factors (ProducedQueryRank.rows p a tail)
        (t.val*p.r+g.val))=
      (List.range p.factors).filter (fun f=>decide (planColor p a tail t f=g)) := by
  unfold LeafHeadSetupProgram.selectedContext
  rw [records_encode_nat,LeafStatisticsProgram.Arity.decoded_encode,query_factor_ids]

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
