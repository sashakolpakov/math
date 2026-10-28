import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedCacheCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteRelation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchMetadata

namespace OAI.Algorithms

/-! A fixed specification for each node of the prepared query. The integer
cache is determined by its width and numeric value; individual executions
remain free to return different sparse representatives of their jets. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
noncomputable section

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ}
    (p : Query.Preparation q k initial hg W V L)
    (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)

def fixedSpec (i : Fin (Query.packingProblem q k hg).Q) :
    Factor.Spec (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q
      (Query.packingProblem q k hg).n ((numeric q k p.lengths).val 34) :=
  nativeSpec q k hg p.firstWord p.remainingWords i p.lengths
    (cacheWords (heads q k hg p.firstWord p.remainingWords i))
    (cacheWords_correct (heads q k hg p.firstWord p.remainingWords i))
    p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced hv source hs

def fixedRelation (i : Fin (Query.packingProblem q k hg).Q) (high : List Bool) :=
  AssignmentConcrete.relation (fixedSpec p hv source hs i) q.forward
    (HighIncidenceProgram.Restriction.zeroMerge q.forward.reverse high).reverse
    LeafStatisticsProgram.Arity.decoded

theorem fixedSpec_parameters (i : Fin (Query.packingProblem q k hg).Q) :
    (fixedSpec p hv source hs i).u=(numeric q k p.lengths).val 33 ∧
    (fixedSpec p hv source hs i).J=(produce (q.input k)).J ∧
    (fixedSpec p hv source hs i).p.R=(produce (q.input k)).R ∧
    (fixedSpec p hv source hs i).p.aWord.length=
      TailInterval.intervalStart (produce (q.input k)).r
        (produce (q.input k)).Q (produce (q.input k)).R :=
  nativeSpec_parameters q k hg p.firstWord p.remainingWords i p.lengths
    (cacheWords _) (cacheWords_correct _) p.modulus p.scalarCache p.half
    p.ringState p.arithmeticOutput.produced hv source hs

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
