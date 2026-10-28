import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostSubstitution
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostComponents
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInputConstruct

namespace OAI.Algorithms

/-! Fixed-polynomial query envelope after substituting the actual setup width
and an explicit uniform node cap. Only the original padded input width remains. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram ProducedQueryResources

 noncomputable def nodeCap {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (occurrence qi C x y z : ℕ) : ℕ :=
  C*(Width.incomingWidth p+1)^x*
    ((resources q k occurrence qi hg p.firstWord p.remainingWords).bits+1)^y*
    (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)+1)^z

 theorem queryCap_produced_polynomial (k CK x y z : ℕ) : ∃ C e : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (occurrence qi : ℕ) (a : Data)
      (hg : Guard (q.input k)) (W V L : ℕ) (p : Preparation q k a hg W V L),
    q.Valid → q.Ready a → (∀i,(a.stacks i).length ≤ W) →
    2 ≤ ambient q → SmallInputs q k (ambient q) →
    V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    queryCap (ordinaryCap p occurrence qi) (nodeCap p occurrence qi CK x y z)
      (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)) ≤
    C*(W+1)^e*(ambient q+1)^((ordinaryExponent+1)*e)*
      (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)+1)^e := by
  obtain ⟨CI,dI,hI⟩ := Width.incoming_width_fixed k
  obtain ⟨CU,dU,hU⟩ := ordinaryCap_fixed k
  obtain ⟨C,e,h⟩ := queryCap_from_node_padding CI dI CU dU CK x y z
  refine ⟨C,e,?_⟩
  intro q occurrence qi a hg W V L p hv hr hw hn hs hV hL
  have hi := hI q occurrence qi a hg W V L p hv hr hw hn hs hV hL
  have hu := hU q occurrence qi a hg W V L p hv hr hw hn hs hV hL
  have ht := h W (resources q k occurrence qi hg p.firstWord p.remainingWords).bits
    (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords))
    (Width.incomingWidth p) (ordinaryCap p occurrence qi) (nodeCap p occurrence qi CK x y z) _
    hi hu (by rfl) (by rfl)
  have hb := FactorResource.produced_bits_succ_le q k occurrence qi hg p.firstWord p.remainingWords hn
  calc
    _ ≤ C*(W+1)^e*((resources q k occurrence qi hg p.firstWord p.remainingWords).bits+1)^e*
        (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)+1)^e := ht
    _ ≤ C*(W+1)^e*((ambient q+1)^(ordinaryExponent+1))^e*
        (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)+1)^e := by gcongr
    _ = _ := by rw [←pow_mul]

 theorem source_reference_le (a : Data) : (a.stacks 321).length ≤ Carried.sourceBytes a := by
  unfold Carried.sourceBytes
  omega

 theorem marked_width_le (a : Data) : Carried.markedWidth a+1 ≤ 11*(Carried.sourceBytes a+1) := by
  have h := source_reference_le a
  unfold Carried.markedWidth
  omega

 theorem accepted_width_le (a : Data) : Carried.acceptedWidth a+1 ≤ 11*(Carried.sourceBytes a+1) := by
  unfold Carried.acceptedWidth
  omega

 theorem source_padding_absorb (C e n work width input : ℕ) (h : width+1 ≤ 11*(input+1)) :
    C*(width+1)^e*(n+1)^((ordinaryExponent+1)*e)*(work+1)^e ≤
      (C*11^e)*(input+1)^e*(n+1)^((ordinaryExponent+1)*e)*(work+1)^e := by
  calc
    _ ≤ C*(11*(input+1))^e*(n+1)^((ordinaryExponent+1)*e)*(work+1)^e := by gcongr
    _ = _ := by rw [mul_pow]; ring

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
