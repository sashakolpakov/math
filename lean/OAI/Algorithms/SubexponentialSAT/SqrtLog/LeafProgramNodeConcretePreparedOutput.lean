import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteQueryPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeDense

namespace OAI.Algorithms

/-! Producer-only single-node semantic endpoint. Its premises are the actual
native preparation, the executed assignment relation, and stored constants. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing LeafParametersProgram MomentsAssembly

 theorem query_prepared_output (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ) (hg : Guard (q.input k))
    (first : MulticolorTypes.Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)) (node : Fin (Query.packingProblem q k hg).Q)
    (a b : Factor.Data) (pr : NodeNative.Preparation (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) a b)
    (m : LeafParametersProgram.Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33)) (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e) (hf : (Query.packingProblem q k hg).Q < 3^(m.val 34))
    (J : ℕ) (hJ : 0 < J) (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (ha : NodeNative.Ready (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) a) (horder : (a.stacks 243).length=J)
    (bits : List Bool) (zero one : RingProgram.Code (Word (baseWidth 3 (m.val 33))) (m.val 34))
    (hz : (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).p.ops.decode zero=0) (ho : (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).p.ops.decode one=1)
    (entries : Relational.Raw 3 (m.val 33) (n:=(Query.packingProblem q k hg).n) (d:=m.val 34))
    (hr : Relational.BucketsRel 3 (m.val 33) M cache (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).ctx.table (m.val 33) J
      (AssignmentConcrete.relation (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs) q.forward bits LeafStatisticsProgram.Arity.decoded zero one)
      pr.supports (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).one pr.bucketInputs [] entries) :
    output 3 (m.val 33) M cache ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).p.model.base (m.val 33))
      (RingBasis.basis ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).p.model.F (m.val 33))) (m.val 33) J entries =
      JetCRT.jet ((PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).p.ops.decode (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs).theta) J
        (specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) m ht hd pr.head.words pr.head.cache M cache half e hp hf q hv J hJ source hs) (planHigh (Query.packingProblem q k hg)) (fun v=>bits.getD v.val.val false)) := by
  apply query_spec_output q hv k hg first tail node m ht hd pr.head.words pr.head.cache
    M cache half e hp hf J hJ source hs pr.head.tables pr.head.count
    (query_preparation_meaning q k hg first tail node a b pr ha)
    bits pr.supports pr.supports_nodup
  · intro S
    rw [pr.supports_all,horder]
  · exact hz
  · exact ho
  · exact hr

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
