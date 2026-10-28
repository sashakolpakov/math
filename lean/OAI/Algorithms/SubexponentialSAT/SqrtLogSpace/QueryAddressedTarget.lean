import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceCoverage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

/-! The actual addressed source, generated ring and complete native factor
inventory instantiate the signed pair target. There is no independently
supplied label kernel, slot assignment, source coverage or evaluator. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAddressedTarget
open scoped BigOperators
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog Polynomial
open MulticolorTypes Subexp.ConstructivePacking SubexpLiftRing SubexpQuarticRing
open LeafHeadSetupProgram LeafParametersProgram LayoutProgram LeafProgram
open SignatureTupleSourceAlignment
variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
local notation "p" => LeafProgram.Query.packingProblem q k hg
variable (first : Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem q k hg).r
    (LeafProgram.Query.packingProblem q k hg).Q))
  (node : Fin (LeafProgram.Query.packingProblem q k hg).Q)
local notation "s" => Native.queryInputsAddressed q k hg first tail node
variable (physical : Data)
  (ready : Native.Ready (Native.queryInputsAddressed q k hg first tail node) physical)
  (bound : ℕ) (bounded : OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed q k hg first tail node).height
    (unary (Native.queryInputsAddressed q k hg first tail node).R)
    (Native.queryInputsAddressed q k hg first tail node).width words)

local notation "src" => QueryHeadSourceFacts.addressedSource q k hg first tail node physical ready bound bounded ra rd rc words hc
section Factor
variable (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (Native.queryInputsAddressed q k hg first tail node).Q < 3^(m.val 34))
    (hv : q.Valid) (hJ : 0 < m.val 42)
    (source : List (List (SAT.Literal (Fin (Native.queryInputsAddressed q k hg first tail node).n))))
    (hsource : q.clauses = HashInputProgram.Expansion.encodedClauses source)
local notation "spec" => QueryReadyConstruction.sourceSpec src m ht hd M cache half e hp
  hfield q hv hJ source hsource
local notation "owner" => ProducedQueryRank.owner p
local notation "sourceOwner" => owner ∘ Fin.cast (Native.Inputs.plans_length s)
local notation "head" => (fun t v => ProducedQueryRank.words p first tail (Sum.inl v) t)
local notation "H" => HighMarkedFrontend.highSet q



local notation "facts" => QueryHeadSourceFacts.sourceFacts q k hg first tail node physical ready
  bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource

/-- The pair loop's actual value is the Taylor jet of the original source
target at the actual generated node, including every neutral factor. -/
theorem signed_pair_target (high : H → Bool) :
    (∑ pair ∈ BooleanDifferences.pairFamily ((s).n - (H).card) (spec).J,
      (-1)^(pair.1.card - pair.2.card) *
        QueryPairEvaluation.pairValue src spec H high sourceOwner head facts pair.1 pair.2) =
      Truncated.ofPolynomial (spec).J ((NodeConcrete.specTarget spec H high).comp
        (X + C ((spec).p.ops.decode (spec).theta))) := by
  refine (QueryPairEvaluation.signed_sum_free src spec H high sourceOwner head facts).trans ?_
  apply QueryEmittedSourceTarget.signed_target src spec H high sourceOwner head facts rfl
    (plans_owner q k hg first tail node)
    (produced_owner_head q k hg first tail node m ht hd words hc M cache half e hp
      hfield hv (m.val 42) hJ source hsource)
    (PreparedSource.nativeSpecOfInputs_theta s m ht hd words hc M cache half e hp
      hfield q hv (m.val 42) hJ source hsource)
    (List.range (s).N) List.nodup_range
    (QueryHeadSourceCoverage.inventory_hashes q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (QueryHeadSourceCoverage.inventory_marked q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (NodeConcrete.planColor p first tail node)
    (QueryHeadSourceSlots.factorIds_eq_color q k hg first tail node)
    (QueryHeadSourceSlots.inventory_slots q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (QueryHeadSourceCoverage.hash_literals q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)
    (QueryHeadSourceCoverage.marked_literals q k hg first tail node physical ready
      bound bounded ra rd rc words hc m ht hd M cache half e hp hfield hv hJ source hsource)

end Factor
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAddressedTarget
