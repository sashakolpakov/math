import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyStorage

namespace OAI.Algorithms

/-! A bounded synthetic assignment reference exists even if no actual
assignment body is visited. It is used only to bound the fixed callback. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open NodeNative LeafHeadSetupProgram MomentsProgram MomentsAssembly NodeEnvelope
attribute [local simp] Fin.coe_ofNat_eq_mod

 def referenceHigh (n : ℕ) (high : Fin 768 → List Bool) : Fin 768 → List Bool :=
  Function.update high 174 (List.replicate n false)

 theorem reference_high_frame (n : ℕ) (high : Fin 768 → List Bool) :
    MomentFrame high (referenceHigh n high) := by
  intro i hi
  have hn : i≠174 := by intro he; subst i; norm_num at hi
  exact Function.update_of_ne hn _ _

 theorem preparation_reference_input {s : HeadInputs} {a b : NodeNative.Data}
    (pr : Preparation s a b) (ha : Ready s a) (input bucketBytes : ℕ)
    (hb : WordBound input a) {d : ℕ} (q : Factor.Spec s.r s.Q s.n d)
    (hf : FactorStatic q a) (hnf : NodeFacts q b.stacks)
    (hprecision : a.stacks 212=List.replicate q.u true)
    (hstream : (bucketsInput pr.bucketInputs).length ≤ bucketBytes)
    (hRQ : q.p.R+1 ≤ s.Q) :
    let A := assignmentCap s input bucketBytes (baseWidth 3 q.p.t) d q.u q.J
    FactorReady.Input q (FactorResource.sourceCap q A A A) A
      (assignmentBase q (List.replicate d true) (referenceHigh s.n b.stacks)) := by
  dsimp only
  let C := memoryCap s input bucketBytes (baseWidth 3 q.p.t) d q.u q.J
  let A := assignmentCap s input bucketBytes (baseWidth 3 q.p.t) d q.u q.J
  have hbase : WordCap C b.stacks :=
    (preparation_wordCap pr ha input bucketBytes q.J hb hf.target hstream).mono
      (by dsimp [C,memoryCap]; omega)
  have hc : ∀i,(Product.tapes (emptyCore (FactorLoop.assignmentEnvironment q
      (List.replicate d true))) i).length ≤ C := by
    intro i
    rw [←preparation_factor_core pr ha q hf hprecision i]
    exact hbase _
  have hh : WordCap C (referenceHigh s.n b.stacks) :=
    hbase.update _ _ (by simp only [List.length_replicate]; dsimp [C,memoryCap]; omega)
  have hpa := preparedAssignment_bound q (List.replicate d true)
    (FactorLoop.maskedHigh (referenceHigh s.n b.stacks)) C hh.masked hc
  have hst := incidence_staged_bound
    (FactorReady.baseData (assignmentBase q (List.replicate d true)
      (referenceHigh s.n b.stacks))) C hpa
  have hs : AssignmentStorage q (List.replicate d true) A (referenceHigh s.n b.stacks) := by
    refine ⟨hpa.mono (by dsimp [A,C,assignmentCap]; omega),hst,?_⟩
    change dictionaryByteEnvelope (baseWidth 3 q.p.t) d (s.n+q.u+q.J)
      (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) q.u q.J) ≤ _
    dsimp [A,assignmentCap,memoryCap]
    omega
  have hn := hnf.frame (reference_high_frame s.n b.stacks)
  have hx : ((referenceHigh s.n b.stacks) 174).length=s.n := by
    simp [referenceHigh]
  have hbound := source_bounds hn hs hRQ
  have hAS : A ≤ FactorResource.sourceCap q A A A :=
    (FactorResource.sourceCap_limits q A A A).base_le_source
  exact hn.input hx hs.1 hs.2.1 hAS (hbound.1.trans hAS) (hbound.2.1.trans hAS)
    (fun x=>⟨(hbound.2.2.1 x).1.trans hAS,(hbound.2.2.1 x).2.1.trans hAS,
      (hbound.2.2.1 x).2.2.trans hAS⟩) (hbound.2.2.2.trans hAS)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
