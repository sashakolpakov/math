import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyPrecision
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyReferenceQuery

namespace OAI.Algorithms

/-! The actual fixed per-node specification supplies both all reachable
assignment contracts and a bounded reference for its uniform cost. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
open NodeNative LeafHeadSetupProgram MomentsAssembly MomentsProgram MomentsAssembly.Relational
noncomputable section


variable {query : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (query.input k)} {W V L : ℕ}
    (p : Query.Preparation query k initial hg W V L)
    (occurrence qi : ℕ) (node : Fin (Query.packingProblem query k hg).Q)
    {a b : NodeNative.Data}
    (pr : Preparation (heads query k hg p.firstWord p.remainingWords node) a b)
    (ha : Ready (heads query k hg p.firstWord p.remainingWords node) a)
    (input : ℕ) (hb : WordBound input a)
    (hr : query.Ready initial) (hp : Persistent p.out a)
    (hv : query.Valid) (hindex : query.index=Encoding.encodeNat (markIndex query))
    (h728 : initial.stacks 728=[])
    (htheta : a.stacks 78=RingProgram.flat (RingNodeProgram.nodeCode
      ((numeric query k p.lengths).val 33) ((numeric query k p.lengths).val 34) (node.val+1)))
    (hhigh : (a.stacks 703).length=(Query.packingProblem query k hg).n)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem query k hg).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)

local notation "q" => fixedSpec p hv source hsource node
local notation "A" => NodeEnvelope.queryStorageCap query k occurrence qi hg p.firstWord p.remainingWords node input

include pr ha hb hr hp hindex h728 htheta hhigh

 theorem query_assignment_frames :
    Reachable.BucketFrames (baseWidth 3 (q).p.t) ((numeric query k p.lengths).val 34)
      Finset.univ (q).u (q).J
      (fun high=>FactorLoop.AssignmentFrame q (List.replicate ((numeric query k p.lengths).val 34) true)
        (FactorResource.sourceCap q A A A) A A A LeafStatisticsProgram.Arity.decoded
        (q).p.ops.zeroRun.1 (q).p.ops.oneRun.1 (b.stacks 702) (b.stacks 703) (FactorLoop.maskedHigh high))
      b.stacks pr.supports pr.bucketInputs := by
  obtain ⟨hf,hnf,hprec⟩ := query_native_facts p node pr ha hr hp hv hindex h728 htheta hhigh source hsource
  have htp : (q).p.t=(numeric query k p.lengths).val 33 :=
    native_spec_precision (heads query k hg p.firstWord p.remainingWords node)
      (numeric query k p.lengths) (Query.ring_precision_pos (query.input k) p.lengths hg)
      (Query.ring_degree_pos (query.input k) p.lengths hg)
      (cacheWords _) (cacheWords_correct _) p.modulus p.scalarCache p.half p.ringState
      p.arithmeticOutput.produced (numeric_field query k p.lengths hg) query hv _
      (produce_J_pos (query.input k)) source hsource
  have ht : (q).p.t=(produce (query.input k)).t := htp.trans (numeric_t query k p.lengths hg)
  have hparams := fixedSpec_parameters p hv source hsource node
  have hu : (q).u=(produce (query.input k)).t := hparams.1.trans (numeric_t query k p.lengths hg)
  have hj : (q).J=(produce (query.input k)).J := hparams.2.1
  have hR : (q).p.R=(produce (query.input k)).R := hparams.2.2.1
  exact query_frames_of_static query k occurrence qi hg p.firstWord p.remainingWords node
    pr ha input hb (d:=(numeric query k p.lengths).val 34) q hf hprec hnf ht
    (numeric_d query k p.lengths hg) hu hj hR

 theorem query_reference_input :
    FactorReady.Input q (FactorResource.sourceCap q A A A) A
      (assignmentBase q (List.replicate ((numeric query k p.lengths).val 34) true)
        (referenceHigh (Query.packingProblem query k hg).n b.stacks)) := by
  obtain ⟨hf,hnf,hprec⟩ := query_native_facts p node pr ha hr hp hv hindex h728 htheta hhigh source hsource
  have htp : (q).p.t=(numeric query k p.lengths).val 33 :=
    native_spec_precision (heads query k hg p.firstWord p.remainingWords node)
      (numeric query k p.lengths) (Query.ring_precision_pos (query.input k) p.lengths hg)
      (Query.ring_degree_pos (query.input k) p.lengths hg)
      (cacheWords _) (cacheWords_correct _) p.modulus p.scalarCache p.half p.ringState
      p.arithmeticOutput.produced (numeric_field query k p.lengths hg) query hv _
      (produce_J_pos (query.input k)) source hsource
  have ht : (q).p.t=(produce (query.input k)).t := htp.trans (numeric_t query k p.lengths hg)
  have hparams := fixedSpec_parameters p hv source hsource node
  have hu : (q).u=(produce (query.input k)).t := hparams.1.trans (numeric_t query k p.lengths hg)
  have hj : (q).J=(produce (query.input k)).J := hparams.2.1
  have hR : (q).p.R=(produce (query.input k)).R := hparams.2.2.1
  exact query_reference_input_of_static query k occurrence qi hg p.firstWord p.remainingWords node
    pr ha input hb (d:=(numeric query k p.lengths).val 34) q hf hprec hnf ht
    (numeric_d query k p.lengths hg) hu hj hR

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
