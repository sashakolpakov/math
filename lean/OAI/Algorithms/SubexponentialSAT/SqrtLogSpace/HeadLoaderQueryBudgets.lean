import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery

/-! Canonical addressed-query rows retain the original ambient and factor counts. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open SqrtLog.LeafHeadSetupProgram

theorem queryInputsAddressed_rows_length (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : MulticolorTypes.Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (LeafProgram.Query.packingProblem q k hg).r
      (LeafProgram.Query.packingProblem q k hg).Q))
    (node : Fin (LeafProgram.Query.packingProblem q k hg).Q) :
    (Native.queryInputsAddressed q k hg first tail node).rows.length =
      (Native.queryInputsAddressed q k hg first tail node).n+
        (Native.queryInputsAddressed q k hg first tail node).N := by
  simp [Native.queryInputsAddressed,Native.queryInputs,ProducedQueryRank.rows,
    PackingCallerProgram.Problem.words_length]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadLoaderBudgets
