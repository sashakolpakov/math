import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteBucketQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryLiterals
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteQueryBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

namespace OAI.Algorithms

/-! The actual query plans, source clauses and produced head tables discharge
all locality and bucket premises of the relational polynomial readout. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT MulticolorTypes SubexpLiftRing SubexpQuarticRing
open MomentsAssembly _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree PackingIncidenceInput
open BucketTupleProgram.Concrete LeafParametersProgram

variable (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ) (hg : Guard (q.input k))
variable (first : Word ((Query.packingProblem q k hg)).r ((Query.packingProblem q k hg)).Q) (tail : List (Word ((Query.packingProblem q k hg)).r ((Query.packingProblem q k hg)).Q)) (node : Fin ((Query.packingProblem q k hg)).Q)
variable (m : LeafParametersProgram.Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node)).height (LeafHeadSetupProgram.unary ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node)).R) ((LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node)).width words)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33)) (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hf : ((Query.packingProblem q k hg)).Q < 3^(m.val 34)) (J : ℕ) (hJ : 0 < J)
    (source : List (List (SAT.Literal (Fin ((Query.packingProblem q k hg)).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)

include q hv k hg first tail node m ht hd words hc M cache half e hp hf J hJ source hs

 theorem query_spec_output
    (tables : List BucketTupleProgram.HeadTable) (hlen : tables.length=((Query.packingProblem q k hg)).r)
    (hm : NativeQueryMeaning q k hg first tail node tables hlen)
    (bits : List Bool)
    (ss : List (Finset (Fin (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node).n)))
    (hss : ss.Nodup)
    (hsmall : ∀ S,S∈ss ↔ S.card < J)
    (zero one : RingProgram.Code (Word (baseWidth 3 (m.val 33))) (m.val 34))
    (hz : ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).p.ops.decode zero=0) (ho : ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).p.ops.decode one=1)
    (entries : Relational.Raw 3 (m.val 33) (n:=((Query.packingProblem q k hg)).n) (d:=m.val 34))
    (hr : Relational.BucketsRel 3 (m.val 33) M cache ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).ctx.table (m.val 33) J
      (AssignmentConcrete.relation (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs) q.forward bits LeafStatisticsProgram.Arity.decoded zero one)
      ss ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).one ((BucketTupleProgram.enumerate tables).map (BucketTupleProgram.Representative.bucket ((Query.packingProblem q k hg)).n)).reverse [] entries)
    :
    output 3 (m.val 33) M cache (((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).p.model.base (m.val 33))
      (RingBasis.basis (((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).p.model.F (m.val 33))) (m.val 33) J entries =
      JetCRT.jet (((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).p.ops.decode ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).theta) J
        (specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs) (planHigh (Query.packingProblem q k hg)) (fun v=>bits.getD v.val.val false)) := by
  have hhashes := query_rows_le_factors q k hg
  have hmarked := query_marked_lt_factors q k hg
  obtain ⟨⟨s,ys,hyn,hyc,he⟩,hmasks,hcontexts⟩ := hm
  have hrel : Relational.BucketsRel 3 (m.val 33) M cache ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).ctx.table (m.val 33) J
      (AssignmentConcrete.relation (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs) q.forward bits LeafStatisticsProgram.Arity.decoded zero one)
      ss ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)).one (ys.map (familyInput s)) [] entries := by rw [he]; exact hr
  apply buckets_specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs) rfl (addressedOwner (Query.packingProblem q k hg)) (addressedOwner_get (Query.packingProblem q k hg))
    (planHead (Query.packingProblem q k hg) first tail) (addressedPlan_head (Query.packingProblem q k hg) first tail) (planHigh (Query.packingProblem q k hg))
    (addressedOwner_low (Query.packingProblem q k hg)) (fun v=>bits.getD v.val.val false) node s hmasks
    (PreparedSource.nativeSpecOfInputs_theta (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd words hc M cache half e hp hf q hv J hJ source hs)
    q.forward bits (planHigh_mask (Query.packingProblem q k hg)) (by intro v; rfl)
    LeafStatisticsProgram.Arity.decoded (List.range ((Query.packingProblem q k hg)).factors) (List.nodup_range) (planColor (Query.packingProblem q k hg) first tail node)
    (addressedPlan_slot (Query.packingProblem q k hg) first tail node)
  · intro id hid hi w hw l hl hlow
    apply query_weighted_literal_present q hv source hs (m.val 33) (m.val 34) id hi w hw l hl
    let v : Fin (Query.packingProblem q k hg).n := Fin.cast (by rfl) l.variable
    have hv : v∉planHigh (Query.packingProblem q k hg) := by
      have heq : v=l.variable := Fin.ext (by rfl)
      rw [heq]
      exact hlow
    change (Query.packingProblem q k hg).mask.getD v.val false=false
    rw [planHigh_mask (Query.packingProblem q k hg) v]
    exact decide_eq_false hv
  · intro hmark hid l hl hlow
    have hzero : q.forward.getD l.variable.val false=false := by
      let v : Fin (Query.packingProblem q k hg).n := Fin.cast (by rfl) l.variable
      have hv : v∉planHigh (Query.packingProblem q k hg) := by
        have heq : v=l.variable := Fin.ext (by rfl)
        rw [heq]
        exact hlow
      change (Query.packingProblem q k hg).mask.getD v.val false=false
      rw [planHigh_mask (Query.packingProblem q k hg) v]
      exact decide_eq_false hv
    have he := query_marked_clause_present q hv source hs hmark l hl hzero
    simpa only [AssignmentConcrete.weightedHashes,List.length_map,PreparedSource.nativeSpecOfInputs,
      PreparedSource.factorSpec,PreparedSource.castRows,
      LeafHeadSetupProgram.Native.queryInputsAddressed_plans,
      LeafHeadSetupProgram.Native.queryInputsAddressed,
      LeafHeadSetupProgram.Native.queryInputs,Query.packingProblem] using he
  · intro i hi
    apply List.mem_range.mpr
    have hi' : i < q.rows.length := by simpa [AssignmentConcrete.weightedHashes,PreparedSource.nativeSpecOfInputs,PreparedSource.factorSpec,PreparedSource.castRows] using hi
    omega
  · intro hmark
    apply List.mem_range.mpr
    simpa [AssignmentConcrete.weightedHashes,PreparedSource.nativeSpecOfInputs,PreparedSource.factorSpec,PreparedSource.castRows] using hmarked hmark
  · intro y g
    rw [(s g).input_context (y g)]
    exact hcontexts g
  · exact hss
  · exact hsmall
  · exact hyn
  · exact hyc
  · exact hz
  · exact ho
  · exact hrel

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
