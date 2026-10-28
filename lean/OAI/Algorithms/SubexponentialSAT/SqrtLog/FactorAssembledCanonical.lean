import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceTapes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceProduced

namespace OAI.Algorithms

/-! One remaining storage cap: the actual bounded reference-state words.
Source, parser, factor-ID, plan, and native arithmetic caps are all computed.
The input-length factor includes arbitrary accepted padding. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing LeafParametersProgram
open SubexponentialSAT.MulticolorTypes ProducedQueryResources PerturbationAssembly

noncomputable def canonicalAssignmentCost {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ) : ℕ :=
  assignmentCost q A A A (nativeCap q A A)

theorem canonical_resource_polynomial : ∃ C e : ℕ, ∀ {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (A U V k : ℕ) (p : CostAssembly.Resources)
    (base : Fin 768 → List Bool),
    FactorReady.Input q (sourceCap q A A A) A base → A ≤ U →
    n ≤ V → baseWidth 3 q.p.t ≤ V → d ≤ V → q.u ≤ V → q.J ≤ V →
    q.J ≤ CostAssembly.jetOrder k n p →
    0 < p.labelBase → 1 ≤ p.heads → 1 ≤ p.bits →
    canonicalAssignmentCost q A ≤ C*(physicalEnvelope U V (CostAssembly.assembledWork k n p)+1)^e := by
  obtain ⟨C,e,he⟩ := assignmentCost_polynomial
  refine ⟨C,e,?_⟩
  intro r Q n d q A U V k p base h hA hn hB hd hu hJ horder hbase hheads hbits
  obtain ⟨hU,h2U,hV,hVV,h100,h10⟩ := physicalEnvelope_bounds U V (CostAssembly.assembledWork k n p)
  apply he q A A A (nativeCap q A A) _ base h (hA.trans hU) (hA.trans hU) (hA.trans hU)
    (nativeCap_le_work q A A U V k p hA hA hn hd hB hu hJ horder hbase hheads hbits)
    (hn.trans hV) (hJ.trans hV)
  · exact (Nat.mul_le_mul hd hB).trans hVV
  · exact (seedBound_le_work k n _ d q.u q.J V p horder hbase hheads hbits hn hB hd hu hJ).trans h10
  · exact (payloadBound_le_base h).trans ((Nat.mul_le_mul_left 2 hA).trans h2U)
  · exact (incidenceTable_le n q.J d _ V hn hJ hd hB).trans h100
  · exact (plans_le_base h).trans (hA.trans hU)

theorem canonical_padding_polynomial : ∃ C e : ℕ, ∀ {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (A input V k a b c : ℕ) (p : CostAssembly.Resources)
    (base : Fin 768 → List Bool),
    FactorReady.Input q (sourceCap q A A A) A base →
    A ≤ paddingEnvelope input V (CostAssembly.assembledWork k n p) a b c →
    n ≤ V → baseWidth 3 q.p.t ≤ V → d ≤ V → q.u ≤ V → q.J ≤ V →
    q.J ≤ CostAssembly.jetOrder k n p →
    0 < p.labelBase → 1 ≤ p.heads → 1 ≤ p.bits →
    canonicalAssignmentCost q A ≤ C*(input+1)^(a*e)*(V+1)^((b+5)*e)*
      (CostAssembly.assembledWork k n p+1)^((c+1)*e) := by
  obtain ⟨C,e,he⟩ := canonical_resource_polynomial
  refine ⟨C*201^e,e,?_⟩
  intro r Q n d q A input V k a b c p base h hA hn hB hd hu hJ horder hbase hheads hbits
  have hb := he q A _ V k p base h hA hn hB hd hu hJ horder hbase hheads hbits
  apply hb.trans
  calc
    _ ≤ C*(201*(input+1)^a*(V+1)^(b+5)*(CostAssembly.assembledWork k n p+1)^(c+1))^e :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left (physicalEnvelope_padding_le input V _ a b c) e)
    _ = _ := by simp only [mul_pow,←pow_mul]; ring

/-- Only the actual masked-state storage bound is external. In particular
there is no source-cost bound, native-cap hypothesis, parser-size hypothesis,
plan-size hypothesis, support-capacity hypothesis or scalar-size hypothesis. -/
theorem produced_canonical_polynomial : ∃ C e : ℕ, ∀
    (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q)),
    query.Valid → 2 ≤ ambient query → SmallInputs query k (ambient query) →
    ∀ {r Q : ℕ} (q : Factor.Spec r Q (ambient query) (produce (query.input k)).d)
    (A input a b c : ℕ) (base : Fin 768 → List Bool),
    q.p.t=(produce (query.input k)).t → q.u=(produce (query.input k)).t →
    q.J=(produce (query.input k)).J →
    FactorReady.Input q (sourceCap q A A A) A base →
    let p := resources query k occurrence qi hg first tail
    A ≤ paddingEnvelope input p.bits (CostAssembly.assembledWork k (ambient query) p) a b c →
    canonicalAssignmentCost q A ≤ C*(input+1)^(a*e)*
      (ambient query+1)^((ordinaryExponent+1)*((b+5)*e))*
      (CostAssembly.assembledWork k (ambient query) p+1)^((c+1)*e) := by
  obtain ⟨C,e,he⟩ := canonical_padding_polynomial
  refine ⟨C,e,?_⟩
  intro query k occurrence qi hg first tail hv hn hs r Q q A input a b c base ht hu hj h
  dsimp only
  intro hA
  let p := resources query k occurrence qi hg first tail
  obtain ⟨hambient,hwidth,hd,hprecision,hjet⟩ :=
    produced_dimensions_le query k occurrence qi hg first tail hn hs
  have hbase : 0 < p.labelBase := by
    change 0 < 2*ambient query*matrixHeight query k+1
    omega
  have hheads : 1 ≤ p.heads := make_heads_pos query k occurrence _ _ _ _ _ _
  have hbits : 1 ≤ p.bits := make_bits_pos query k occurrence _ _ _ _ _ _
  have hb := he q A input p.bits k a b c p base h hA hambient
    (by simpa only [ht] using hwidth) hd (by simpa only [hu] using hprecision)
    (by simpa only [hj] using hjet)
    (by rw [hj]; exact (produced_order_eq query k occurrence qi hg first tail hv).le)
    hbase hheads hbits
  apply hb.trans
  have hp := Nat.pow_le_pow_left (produced_bits_succ_le query k occurrence qi hg first tail hn) ((b+5)*e)
  rw [←pow_mul] at hp
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
