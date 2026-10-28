import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryFrontState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeQuery

namespace OAI.Algorithms

/-! Exact scalar fields shared by the native frontend and physical heads. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
open LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

 theorem query_factors (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) :
    (q.input k).factors=(Query.packingProblem q k hg).factors := by
  have h := PackingIncidenceInput.Stats.native_factor_count q.scopeRows q.forward
  simpa [Query.packingProblem,PackingCallerProgram.Problem.factors,
    LeafQueryFrontend.Query.input,LeafQueryFrontend.numericInput,LeafQueryFrontend.totals,
    LeafStatisticsProgram.zeroTotals,PackingIncidenceInput.Stats.zero] using h.symm

 theorem frontend_scalars (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Query.Data)
    (l : Fin 8 → ℕ) (w : Bank.Words) (hf : Query.FrontState q k a b l w)
    (hg : Guard (q.input k)) :
    b.stacks 128=unary (Query.packingProblem q k hg).n ∧
    b.stacks 129=unary (Query.packingProblem q k hg).factors ∧
    b.stacks 130=unary (Query.packingProblem q k hg).r ∧
    b.stacks 131=unary (Query.packingProblem q k hg).Q ∧
    b.stacks 132=unary ((Query.packingProblem q k hg).Q*(Query.packingProblem q k hg).r) ∧
    b.stacks 138=unary (produce (q.input k)).R ∧
    b.stacks 139=unary (Subexp.TailInterval.intervalStart (produce (q.input k)).r
      (produce (q.input k)).Q (produce (q.input k)).R) ∧
    b.stacks 140=unary (1+2*Subexp.TailInterval.intervalStart (produce (q.input k)).r
      (produce (q.input k)).Q (produce (q.input k)).R*(produce (q.input k)).R+
        (produce (q.input k)).Q) ∧
    BinaryArithmetic.toNat (b.stacks 141)=
      2*(q.input k).occurrence*(8*(produce (q.input k)).Q)^(2*(produce (q.input k)).R) := by
  have h0 : (Execute.guardedModel (q.input k) l).val 0=(q.input k).ambient := Execute.guardedModel_input (q.input k) l 0
  have h3 : (Execute.guardedModel (q.input k) l).val 3=(q.input k).occurrence := Execute.guardedModel_input (q.input k) l 3
  have h5 : (Execute.guardedModel (q.input k) l).val 5=(q.input k).factors := Execute.guardedModel_input (q.input k) l 5
  have hr : (Execute.guardedModel (q.input k) l).val 18=(produce (q.input k)).r := Execute.guardedModel_radius (q.input k) l
  have hq : (Execute.guardedModel (q.input k) l).val 21=(produce (q.input k)).Q := (Execute.guardedModel_public (q.input k) l 4).trans
    (Layout.model_core_values (q.input k) l).2.2.2.2.1
  have hR : (Execute.guardedModel (q.input k) l).val 29=(produce (q.input k)).R := (Execute.guardedModel_public (q.input k) l 6).trans
    (Layout.model_core_values (q.input k) l).2.2.2.2.2.2.1
  have hi := LeafQueryFrontend.exported_input_values (q.input k) l b hf.exported
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [unary,Query.packingProblem,LeafQueryFrontend.Query.input,
      LeafQueryFrontend.numericInput] using hi.1
  · simpa [unary,query_factors q k hg] using hi.2.1
  · simpa [Exports.destination,Exports.unaryValues,hr,unary,Query.packingProblem] using hf.exported.1 2
  · simpa [Exports.destination,Exports.unaryValues,hq,unary,Query.packingProblem] using hf.exported.1 3
  · simpa [Exports.destination,Exports.unaryValues,hq,hr,unary,Query.packingProblem] using hf.exported.1 4
  · simpa [Exports.destination,Exports.unaryValues,hR,unary] using hf.exported.1 5
  · simpa [Exports.destination,Exports.unaryValues,hq,hr,hR,unary] using hf.exported.1 6
  · simpa [Exports.destination,Exports.unaryValues,hq,hr,hR,unary] using hf.exported.1 7
  · simpa only [h3,hq,hR] using hf.offset
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end OAI.Algorithms
