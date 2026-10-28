import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimePrepared
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyPrecision

namespace OAI.Algorithms

/-! The measured full node budget at the actual fixed-cache specification.
All remaining hypotheses are physical query/collector interfaces. -/
namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open LeafProgram LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
open NodeNative LeafHeadSetupProgram MomentsAssembly MomentsProgram PreparedReady
noncomputable section

 theorem native_fullBudget_polynomial : ∃ C x y z : ℕ, ∀
    {query : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (query.input k)} {W V L : ℕ}
    (p : Query.Preparation query k initial hg W V L)
    (occurrence qi : ℕ) (node : Fin (Query.packingProblem query k hg).Q)
    {a b : NodeNative.Data}
    (pr : Preparation (heads query k hg p.firstWord p.remainingWords node) a b)
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
      C*(input+1)^x*(resources.bits+1)^y*
        (CostAssembly.assembledWork k (ProducedQueryResources.ambient query) resources+1)^z := by
  obtain ⟨C,x,y,z,h⟩ := prepared_fullBudget_polynomial
  refine ⟨C,x,y,z,?_⟩
  intro query k initial hg W V L p occurrence qi node a b pr ha input hb hr hp hv hn hs
    hindex h728 htheta hhigh source hsource
  dsimp only
  let q := nativeSpec query k hg p.firstWord p.remainingWords node p.lengths
    (cacheWords (heads query k hg p.firstWord p.remainingWords node))
    (cacheWords_correct (heads query k hg p.firstWord p.remainingWords node))
    p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced hv source hsource
  obtain ⟨hf,hnf,hprec⟩ := query_native_facts p node pr ha hr hp hv hindex h728 htheta hhigh source hsource
  have htp : q.p.t=(numeric query k p.lengths).val 33 :=
    native_spec_precision (heads query k hg p.firstWord p.remainingWords node)
      (numeric query k p.lengths) (Query.ring_precision_pos (query.input k) p.lengths hg)
      (Query.ring_degree_pos (query.input k) p.lengths hg)
      (cacheWords _) (cacheWords_correct _) p.modulus p.scalarCache p.half p.ringState
      p.arithmeticOutput.produced (numeric_field query k p.lengths hg) query hv _
      (produce_J_pos (query.input k)) source hsource
  have hparams := fixedSpec_parameters p hv source hsource node
  exact h query k occurrence qi hg p.firstWord p.remainingWords node pr ha input hb hv hn hs q
    hf hnf hprec (htp.trans (numeric_t query k p.lengths hg)) (numeric_d query k p.lengths hg)
    (hparams.1.trans (numeric_t query k p.lengths hg)) hparams.2.1 hparams.2.2.1

end
end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
