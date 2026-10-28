import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostFinal

namespace OAI.Algorithms

/-! Fix the universal coefficients from the actual native-node cost theorem
once. Their choice precedes every query, mark, input and padding length. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open LeafProgram LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
open NodeNative LeafHeadSetupProgram MomentsAssembly MomentsProgram PreparedReady
noncomputable section

 def nodeCoefficient : ℕ := Classical.choose NodeTime.native_fullBudget_polynomial
 def nodeInputExponent : ℕ := Classical.choose (Classical.choose_spec NodeTime.native_fullBudget_polynomial)
 def nodeScalarExponent : ℕ := Classical.choose
  (Classical.choose_spec (Classical.choose_spec NodeTime.native_fullBudget_polynomial))
 def nodeWorkExponent : ℕ := Classical.choose
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec NodeTime.native_fullBudget_polynomial)))

 theorem selected_native_node_bound : ∀
    {query : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (query.input k)} {W V L : ℕ}
    (p : Query.Preparation query k initial hg W V L)
    (occurrence qi : ℕ) (node : Fin (Query.packingProblem query k hg).Q)
    {a b : NodeNative.Data}
    (pr : NodeNative.Preparation (heads query k hg p.firstWord p.remainingWords node) a b)
    (_ha : Ready (heads query k hg p.firstWord p.remainingWords node) a)
    (input : ℕ), WordBound input a →
    query.Ready initial → Persistent p.out a →
    ∀ (hv : query.Valid), 2 ≤ ProducedQueryResources.ambient query →
    ProducedQueryResources.SmallInputs query k (ProducedQueryResources.ambient query) →
    query.index=Encoding.encodeNat (markIndex query) → initial.stacks 728=[] →
    a.stacks 78=RingProgram.flat (RingNodeProgram.nodeCode
      ((numeric query k p.lengths).val 33) ((numeric query k p.lengths).val 34) (node.val+1)) →
    (a.stacks 703).length=(Query.packingProblem query k hg).n →
    ∀ (source : List (List (SAT.Literal (Fin (Query.packingProblem query k hg).n))))
      (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source),
    let q := nativeSpec query k hg p.firstWord p.remainingWords node p.lengths
      (cacheWords (heads query k hg p.firstWord p.remainingWords node))
      (cacheWords_correct (heads query k hg p.firstWord p.remainingWords node))
      p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced hv source hsource
    let A := NodeEnvelope.queryStorageCap query k occurrence qi hg p.firstWord p.remainingWords node input
    let resources := ProducedQueryResources.resources query k occurrence qi hg p.firstWord p.remainingWords
    fullBudget pr (baseWidth 3 q.p.t) ((numeric query k p.lengths).val 34) q.u q.J
      A A A (FactorResource.canonicalAssignmentCost q A) A ≤
      nodeCoefficient*(input+1)^nodeInputExponent*(resources.bits+1)^nodeScalarExponent*
        (CostAssembly.assembledWork k (ProducedQueryResources.ambient query) resources+1)^nodeWorkExponent := by
  exact Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec NodeTime.native_fullBudget_polynomial)))

 theorem marked_fixed_polynomial (k : ℕ) :
    type_of% (marked_polynomial k nodeCoefficient nodeInputExponent
      nodeScalarExponent nodeWorkExponent) :=
  marked_polynomial k nodeCoefficient nodeInputExponent nodeScalarExponent nodeWorkExponent

 theorem accepted_fixed_polynomial (k : ℕ) :
    type_of% (accepted_polynomial k nodeCoefficient nodeInputExponent
      nodeScalarExponent nodeWorkExponent) :=
  accepted_polynomial k nodeCoefficient nodeInputExponent nodeScalarExponent nodeWorkExponent

end
end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
