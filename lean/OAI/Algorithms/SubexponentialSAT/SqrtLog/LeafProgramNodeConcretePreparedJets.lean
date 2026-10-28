import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcretePreparedOutput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSharedTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecBounds

namespace OAI.Algorithms

/-! Actual independently produced node dictionaries supply all reconstruction
jets of one fixed source target. No raw-output uniqueness is required. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open SubexponentialSAT MulticolorTypes SubexpLiftRing SubexpQuarticRing LeafParametersProgram MomentsAssembly

 theorem query_prepared_hasJets
    (q : LeafQueryFrontend.Query) (hv : q.Valid) (k : ℕ) (hg : Guard (q.input k))
    (first : MulticolorTypes.Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)
    (tail : List (MulticolorTypes.Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q))
    (a b : Fin (Query.packingProblem q k hg).Q → Factor.Data)
    (pr : ∀ i,NodeNative.Preparation (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) (a i) (b i))
    (ha : ∀ i,NodeNative.Ready (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) (a i))
    (m : LeafParametersProgram.Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33)) (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e) (hf : (Query.packingProblem q k hg).Q < 3^(m.val 34))
    (J : ℕ) (hJ : 0 < J) (horder : ∀ i,((a i).stacks 243).length=J)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (bits : List Bool) (zero one : RingProgram.Code (SubexpQuarticRing.Word (baseWidth 3 (m.val 33))) (m.val 34))
    (hz : (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode zero=0) (ho : (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode one=1)
    (entries : Fin (Query.packingProblem q k hg).Q → Relational.Raw 3 (m.val 33) (n:=(Query.packingProblem q k hg).n) (d:=m.val 34))
    (hr : ∀ i,Relational.BucketsRel 3 (m.val 33) M cache (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd (pr i).head.words (pr i).head.cache M cache half e hp hf q hv J hJ source hs).ctx.table (m.val 33) J
      (AssignmentConcrete.relation (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd (pr i).head.words (pr i).head.cache M cache half e hp hf q hv J hJ source hs) q.forward bits LeafStatisticsProgram.Arity.decoded zero one)
      (pr i).supports (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd (pr i).head.words (pr i).head.cache M cache half e hp hf q hv J hJ source hs).one (pr i).bucketInputs [] (entries i))
    (base : Fin (Query.packingProblem q k hg).Q) :
    Reconstruction.HasJets (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache)
      (fun i : Fin (Query.packingProblem q k hg).Q=>RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1)) J
      (fun i=>MomentsReadoutProgram.outputCodes 3 (m.val 33) M cache (entries i) (m.val 33) zero 0 J)
      (specTarget (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail base) m ht hd (pr base).head.words (pr base).head.cache M cache half e hp hf q hv J hJ source hs) (planHigh (Query.packingProblem q k hg)) (fun v=>bits.getD v.val.val false)) := by
  intro i
  have hout := query_prepared_output q hv k hg first tail i (a i) (b i) (pr i)
    m ht hd M cache half e hp hf J hJ source hs (ha i) (horder i) bits zero one hz ho (entries i) (hr i)
  have he := query_target_independent q hv k hg first tail i base m ht hd
    (pr i).head.words (pr base).head.words (pr i).head.cache (pr base).head.cache
    M cache half e hp hf J hJ source hs (planHigh (Query.packingProblem q k hg)) (fun v=>bits.getD v.val.val false)
  have hout' := hout.trans (congrArg
    (JetCRT.jet ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
      (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))) J) he)
  have hn := Relational.buckets_nodup 3 (m.val 33) M cache (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd (pr i).head.words (pr i).head.cache M cache half e hp hf q hv J hJ source hs).ctx.table
    (m.val 33) J (AssignmentConcrete.relation (PreparedSource.nativeSpecOfInputs (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail i) m ht hd (pr i).head.words (pr i).head.cache M cache half e hp hf q hv J hJ source hs) q.forward bits LeafStatisticsProgram.Arity.decoded zero one)
    (hr i) (by simp [Squarefree.Sparse.keys])
  have hc := NodeSemantics.outputCodes_polynomial 3 (m.val 33) M cache ((IrreducibleSearch.data hd).base (m.val 33))
    (RingBasis.basis ((IrreducibleSearch.data hd).F (m.val 33))) (m.val 33) J (entries i) zero hn hz
  change Truncation.trunc J (PolynomialAlgorithm.denote
    ((MomentsReadoutProgram.outputCodes 3 (m.val 33) M cache (entries i) (m.val 33) zero 0 J).map
      (RingProgram.denote (RingProgram.scalarRing 3 (m.val 33) M cache)
        ((IrreducibleSearch.data hd).base (m.val 33)) (RingBasis.basis ((IrreducibleSearch.data hd).F (m.val 33)))))) = _
  have hj := TruncatedInverse.jet_eq_trunc
    ((RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
      (RingNodeProgram.nodeCode (m.val 33) (m.val 34) (i.val+1))) J
    (specTarget (PreparedSource.nativeSpecOfInputs
      (LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail base)
      m ht hd (pr base).head.words (pr base).head.cache M cache half e hp hf
      q hv J hJ source hs) (planHigh (Query.packingProblem q k hg))
      (fun v=>bits.getD v.val.val false))
  exact (congrArg (Truncation.trunc J) (hc.trans hout')).trans
    ((congrArg (Truncation.trunc J) hj).trans
      ((TruncatedInverse.trunc_idempotent J _).trans hj.symm))

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
