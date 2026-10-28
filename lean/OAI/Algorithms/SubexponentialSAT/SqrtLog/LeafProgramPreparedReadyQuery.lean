import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyStatic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyCanonical
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryDegree

namespace OAI.Algorithms

/-! Actual query and head preparations imply every reachable factor/source
readiness contract. Only the physical node/high-assignment bytes and the
producer's exact degree word are used, not a readiness or execution oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
open NodeNative LeafHeadSetupProgram MomentsAssembly MomentsProgram MomentsAssembly.Relational
noncomputable section

 theorem query_native_facts
    {query : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (query.input k)} {W V L : ℕ}
    (p : Query.Preparation query k initial hg W V L)
    (node : Fin (Query.packingProblem query k hg).Q)
    {a b : NodeNative.Data}
    (pr : Preparation (heads query k hg p.firstWord p.remainingWords node) a b)
    (ha : Ready (heads query k hg p.firstWord p.remainingWords node) a)
    (hr : query.Ready initial) (hp : Persistent p.out a)
    (hv : query.Valid) (hindex : query.index=Encoding.encodeNat (markIndex query))
    (h728 : initial.stacks 728=[])
    (htheta : a.stacks 78=RingProgram.flat (RingNodeProgram.nodeCode
      ((numeric query k p.lengths).val 33) ((numeric query k p.lengths).val 34) (node.val+1)))
    (hhigh : (a.stacks 703).length=(Query.packingProblem query k hg).n)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem query k hg).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source) :
    let q := nativeSpec query k hg p.firstWord p.remainingWords node p.lengths
      (cacheWords (heads query k hg p.firstWord p.remainingWords node))
      (cacheWords_correct (heads query k hg p.firstWord p.remainingWords node))
      p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced hv source hsource
    FactorStatic (s:=heads query k hg p.firstWord p.remainingWords node) q a ∧
      NodeFacts q b.stacks ∧ a.stacks 212=List.replicate q.u true := by
  dsimp only
  let q := nativeSpec query k hg p.firstWord p.remainingWords node p.lengths
    pr.head.words pr.head.cache p.modulus p.scalarCache p.half p.ringState
    p.arithmeticOutput.produced hv source hsource
  have hR : (p.packed.stacks 740).length=
      (heads query k hg p.firstWord p.remainingWords node).R := by
    rw [p.cutoff,List.length_replicate]
    rfl
  have hdegree : p.ringState.stacks 204=List.replicate ((numeric query k p.lengths).val 34) true :=
    (p.arithmeticOutput.low 204 (by decide)).symm.trans (p.degree h728)
  have hf : FactorStatic (s:=heads query k hg p.firstWord p.remainingWords node) q a := native_static_of_arithmetic
    (heads query k hg p.firstWord p.remainingWords node) (numeric query k p.lengths)
    (Query.ring_precision_pos (query.input k) p.lengths hg)
    (Query.ring_degree_pos (query.input k) p.lengths hg)
    pr.head.words pr.head.cache p.modulus p.scalarCache p.half p.ringState
    p.packed p.out a p.arithmeticOutput (numeric_field query k p.lengths hg)
    (numeric_Q query k p.lengths) hR hp query hv _ (produce_J_pos (query.input k))
    (numeric_J query k p.lengths hg) source hsource ((query_fields p hr).frame hp)
    hindex hdegree htheta hhigh
  have hnf : NodeFacts q b.stacks := preparation_native_facts pr ha
    (numeric query k p.lengths) (Query.ring_precision_pos (query.input k) p.lengths hg)
    (Query.ring_degree_pos (query.input k) p.lengths hg)
    p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
    (numeric_field query k p.lengths hg) query hv _ (produce_J_pos (query.input k)) source hsource hf
  have hprecision' : a.stacks 212=List.replicate ((numeric query k p.lengths).val 33) true :=
    (hp 212 (by decide)).trans ((p.arithmeticOutput.low 212 (by decide)).trans
      p.arithmeticOutput.produced.caches.precision)
  have hu : q.u=(numeric query k p.lengths).val 33 :=
    (nativeSpec_parameters query k hg p.firstWord p.remainingWords node p.lengths
      pr.head.words pr.head.cache p.modulus p.scalarCache p.half p.ringState
      p.arithmeticOutput.produced hv source hsource).1
  have hprecision : a.stacks 212=List.replicate q.u true :=
    hprecision'.trans (congrArg (fun u => List.replicate u true) hu.symm)
  have heq : q=nativeSpec query k hg p.firstWord p.remainingWords node p.lengths
      (cacheWords (heads query k hg p.firstWord p.remainingWords node))
      (cacheWords_correct (heads query k hg p.firstWord p.remainingWords node))
      p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced hv source hsource :=
    native_spec_words_congr (heads query k hg p.firstWord p.remainingWords node)
      (numeric query k p.lengths) (Query.ring_precision_pos (query.input k) p.lengths hg)
      (Query.ring_degree_pos (query.input k) p.lengths hg) pr.head.words _ pr.head.cache
      (cacheWords_correct _) (cacheWords_eq _ pr.head.cache) p.modulus p.scalarCache p.half
      p.ringState p.arithmeticOutput.produced (numeric_field query k p.lengths hg)
      query hv _ (produce_J_pos (query.input k)) source hsource
  exact ⟨heq ▸ hf,heq ▸ hnf,heq ▸ hprecision⟩

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
