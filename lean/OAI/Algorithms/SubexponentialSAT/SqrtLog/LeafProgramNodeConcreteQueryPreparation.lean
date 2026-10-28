import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteQueryNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeWords

namespace OAI.Algorithms

/-! The produced native preparation directly supplies the complete attained
bucket family, canonical masks and the exact ordered factor contexts. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT.MulticolorTypes
open BucketTupleProgram.Concrete

 theorem query_preparation_meaning
    (q : LeafQueryFrontend.Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (first : Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)
    (tail : List (Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q)
    (a b : Factor.Data)
    (pr : NodeNative.Preparation (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) a b)
    (ha : NodeNative.Ready (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node) a) :
    NativeQueryMeaning q k hg first tail node pr.head.tables pr.head.count := by
  have hr := NodeNative.ready_congr _ pr.loaded_words.symm ha.heads
  exact native_query_started q k hg first tail node (LeafHeadSetupProgram.Native.project pr.loaded) hr
    pr.head.ra pr.head.rd pr.head.rc pr.head.words pr.head.produced pr.head.count

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
