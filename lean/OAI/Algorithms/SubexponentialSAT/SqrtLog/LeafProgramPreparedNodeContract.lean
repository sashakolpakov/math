import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedAssignment
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodePostModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryDegree
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodeFamily

namespace OAI.Algorithms

/-! The fixed assignment contract used at every node of the actual collector. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing MomentsAssembly
noncomputable section
attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)
    (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)

local notation "ctx" => nodeArithmetic q k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced

theorem prepared_assignment_contract (occurrence qi : ℕ)
    (i : Fin (Query.packingProblem q k hg).Q) (high : List Bool)
    (h728 : initial.stacks 728=[]) :
    Relational.AssignmentContract 3 (ctx).t (ctx).modulus (ctx).cache (ctx).table (ctx).u (ctx).J
      (fixedRelation p hv source hs i high (ctx).zero (ctx).one)
      Factor.assignment (ctx).degree (ctx).width Finset.univ
      (PreparedNodePost.collectorFrame p occurrence qi hv source hs i high)
      (FactorResource.canonicalAssignmentCost (fixedSpec p hv source hs i)
        (PreparedNodePost.storageCap p occurrence qi i)) := by
  have hd : p.ringState.stacks 204=List.replicate ((numeric q k p.lengths).val 34) true :=
    (p.arithmeticOutput.low 204 (by decide)).symm.trans (p.degree h728)
  refine (congrArg (fun degree=>
    Relational.AssignmentContract 3 (ctx).t (ctx).modulus (ctx).cache (ctx).table (ctx).u (ctx).J
      (fixedRelation p hv source hs i high (ctx).zero (ctx).one)
      Factor.assignment degree (ctx).width Finset.univ
      (PreparedNodePost.collectorFrame p occurrence qi hv source hs i high)
      (FactorResource.canonicalAssignmentCost (fixedSpec p hv source hs i)
        (PreparedNodePost.storageCap p occurrence qi i))) hd).mpr ?_
  exact canonical_assignment_contract (fixedSpec p hv source hs i)
    (List.replicate ((numeric q k p.lengths).val 34) true)
    (PreparedNodePost.storageCap p occurrence qi i) LeafStatisticsProgram.Arity.decoded
    (ctx).zero (ctx).one q.forward
    (HighIncidenceProgram.Restriction.zeroMerge q.forward.reverse high).reverse

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
