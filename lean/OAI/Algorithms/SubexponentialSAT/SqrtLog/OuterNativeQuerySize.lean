import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQueryRuntime
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeLocalBounds

namespace OAI.Algorithms

/-! Query costs use only copied source words, not the arbitrary selector
incumbent, queue, or register-save tail. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram LeafOuterNative

 theorem sourceBytes_le (q : LeafQueryFrontend.Query) (a : Query.Data)
    (hs : Query.Sources q a) (hr : (a.stacks 321).length ≤ q.index.length) :
    Query.Carried.sourceBytes a ≤ queryBytes q := by
  simp only [Query.Carried.sourceBytes,queryBytes,hs.formula,hs.rows,hs.modulus,
    hs.width,hs.ambient]
  omega

 theorem trial_queryBytes_le {q : LeafQueryFrontend.Query} {a : LeafOuterProgram.Data} {L J : ℕ}
    (h : OuterQuery.TrialWords q a)
    (hs : ∀ i, MassSource i → (a.stacks i).length ≤ L)
    (hi : q.index.length ≤ J) : queryBytes q ≤ 7*L+J+2 := by
  have h0 := hs 768 (by decide)
  have h1 := hs 777 (by decide)
  have h2 := hs 782 (by decide)
  have h3 := hs 783 (by decide)
  have h4 := hs 784 (by decide)
  have h5 := hs 785 (by decide)
  have rows := congrArg List.length h.rows
  simp only [List.length_cons,List.length_append,Encoding.length_frame,List.length_reverse] at rows
  rw [h.modulus] at h2
  rw [h.width] at h3
  rw [h.formula] at h4
  rw [h.ambient] at h5
  unfold queryBytes
  omega

 theorem final_queryBytes_le {q : LeafQueryFrontend.Query} {a : LeafOuterProgram.Data} {L J : ℕ}
    (h : OuterQuery.FinalWords q a)
    (hf : (a.stacks 784).length ≤ L) (hr : (a.stacks 777).length ≤ L)
    (hm : (a.stacks 782).length ≤ L) (hw : (a.stacks 783).length ≤ L)
    (hn : (a.stacks 785).length ≤ L) (hi : q.index.length ≤ J) :
    queryBytes q ≤ 5*L+J := by
  rw [h.formula] at hf
  rw [h.rows] at hr
  rw [h.modulus] at hm
  rw [h.width] at hw
  rw [h.ambient] at hn
  unfold queryBytes
  omega

 theorem runtimeBound_mono_input {C A : ℝ} (hC : 0 ≤ C) (e n : ℕ)
    {x y : ℕ} (hxy : x ≤ y) :
    Statement.runtimeBound C A e x n ≤ Statement.runtimeBound C A e y n := by
  unfold Statement.runtimeBound
  gcongr

 theorem queryLimit_le {k qi C e W : ℕ} {q : LeafQueryFrontend.Query}
    (hw : queryBytes q ≤ W) : queryLimit k qi C e q ≤
      Nat.ceil (Statement.runtimeBound (ProducedQueryResources.runtimeCoefficient C e)
        (ProducedQueryResources.runtimeExponent k qi e) e W (ProducedQueryResources.ambient q)) := by
  apply Nat.ceil_mono
  apply runtimeBound_mono_input
  · unfold ProducedQueryResources.runtimeCoefficient
    positivity
  · exact hw

 theorem RuntimeFacts.source_cost_le {q : LeafQueryFrontend.Query} {k B qi C e : ℕ}
    (h : RuntimeFacts q k B qi C e) (a : Query.Data)
    (hs : Query.Sources q a) (hr : (a.stacks 321).length ≤ q.index.length)
    (hg : LeafParametersProgram.Guard (q.input k))
    (first : MulticolorTypes.Word (ProducedQueryResources.problem q k hg).r
      (ProducedQueryResources.problem q k hg).Q)
    (tail : List (MulticolorTypes.Word (ProducedQueryResources.problem q k hg).r
      (ProducedQueryResources.problem q k hg).Q))
    (hN : (first::tail).Nodup) (hA : ∀ z,z∈first::tail) :
    C*(Query.Carried.sourceBytes a+1)^e*(ProducedQueryResources.ambient q+1)^
      ((ProducedQueryResources.ordinaryExponent+1)*e)*
      (CostAssembly.assembledWork k (ProducedQueryResources.ambient q)
        (ProducedQueryResources.resources q k B qi hg first tail)+1)^e ≤ queryLimit k qi C e q := by
  apply le_trans _ (h.cost hg first tail hN hA)
  have hb := sourceBytes_le q a hs hr
  gcongr

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
