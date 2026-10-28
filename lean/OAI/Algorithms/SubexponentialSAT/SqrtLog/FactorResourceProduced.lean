import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorAssembledBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCoreBound

namespace OAI.Algorithms

/-! The numeric and support parameters of the actual query resource record.
The only external size interface left is the bounded prepared node state. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing LeafParametersProgram
open SubexponentialSAT.MulticolorTypes
open ProducedQueryResources

variable (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))

theorem produced_order_eq (hv : query.Valid) :
    (produce (query.input k)).J =
      CostAssembly.jetOrder k (ambient query) (resources query k occurrence qi hg first tail) := by
  unfold produce CostAssembly.jetOrder CostAssembly.jetNumerator resources ofPacking make
  dsimp only
  rw [input_ambient,input_width,input_clauses query k hv]

/-- All scalar dimensions used by the native sparse evaluator are actual
values from the serialized parameter bank. -/
theorem produced_dimensions_le (hn : 2 ≤ ambient query)
    (hs : SmallInputs query k (ambient query)) :
    ambient query ≤ (resources query k occurrence qi hg first tail).bits ∧
    baseWidth 3 (produce (query.input k)).t ≤ (resources query k occurrence qi hg first tail).bits ∧
    (produce (query.input k)).d ≤ (resources query k occurrence qi hg first tail).bits ∧
    (produce (query.input k)).t ≤ (resources query k occurrence qi hg first tail).bits ∧
    (produce (query.input k)).J ≤ (resources query k occurrence qi hg first tail).bits := by
  let l : Fin 8 → ℕ := query.inputLengths k
  have ht := values_le_resources query k occurrence qi (ambient query) hn rfl hs hg first tail l 33
  have hd := values_le_resources query k occurrence qi (ambient query) hn rfl hs hg first tail l 34
  have hj := values_le_resources query k occurrence qi (ambient query) hn rfl hs hg first tail l 42
  have hb := values_le_resources query k occurrence qi (ambient query) hn rfl hs hg first tail l 45
  rw [Serialization.frame _ 33 (by decide) (by decide)] at ht
  rw [Serialization.frame _ 34 (by decide) (by decide)] at hd
  rw [Serialization.frame _ 42 (by decide) (by decide)] at hj
  rw [(Serialization.values _).2] at hb
  change (PreparedSource.numeric query k l).val 33 ≤ _ at ht
  change (PreparedSource.numeric query k l).val 34 ≤ _ at hd
  change (PreparedSource.numeric query k l).val 42 ≤ _ at hj
  change 2*(PreparedSource.numeric query k l).val 33 ≤ _ at hb
  rw [PreparedSource.numeric_t query k l hg] at ht hb
  rw [PreparedSource.numeric_d query k l hg] at hd
  rw [PreparedSource.numeric_J query k l hg] at hj
  refine ⟨?_,?_,hd,ht,hj⟩
  · change ambient query ≤ (ambient query+1)^ordinaryExponent
    have he := ordinaryExponent_ge
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ ambient query+1)
      (show 1 ≤ ordinaryExponent by omega)
    simp only [pow_one] at hp
    exact (Nat.le_succ (ambient query)).trans hp
  · have hlog : Nat.log 2 3=1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    simpa [baseWidth,hlog,Nat.mul_comm] using hb

theorem produced_bits_succ_le (hn : 2 ≤ ambient query) :
    (resources query k occurrence qi hg first tail).bits+1 ≤
      (ambient query+1)^(ordinaryExponent+1) := by
  change (ambient query+1)^ordinaryExponent+1 ≤ _
  have hp : 1 ≤ (ambient query+1)^ordinaryExponent := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ]
  nlinarith

/-- A complete measured assignment bound for a Spec with the actual produced
numeric parameters. The remaining five caps refer to the masked node base,
parser tail, factor IDs, native scalar/payload cap, and physical plan stream. -/
theorem produced_assignment_polynomial : ∃ C e : ℕ, ∀
    (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q)),
    query.Valid → 2 ≤ ambient query → SmallInputs query k (ambient query) →
    ∀ {r Q : ℕ} (q : Factor.Spec r Q (ambient query) (produce (query.input k)).d)
    (A T F Z input a b c : ℕ) (base : Fin 768 → List Bool),
    q.p.t=(produce (query.input k)).t → q.u=(produce (query.input k)).t →
    q.J=(produce (query.input k)).J →
    FactorReady.Input q (sourceCap q A T F) A base →
    let p := resources query k occurrence qi hg first tail
    let U := paddingEnvelope input p.bits (CostAssembly.assembledWork k (ambient query) p) a b c
    A ≤ U → T ≤ U → F ≤ U → Z ≤ U →
    (LayoutOwnerFiberProgram.stream q.ps).length ≤ U →
    assignmentCost q A T F Z ≤ C*(input+1)^(a*e)*
      (ambient query+1)^((ordinaryExponent+1)*((b+5)*e))*
      (CostAssembly.assembledWork k (ambient query) p+1)^((c+1)*e) := by
  obtain ⟨C,e,he⟩ := assignmentCost_padding_polynomial
  refine ⟨C,e,?_⟩
  intro query k occurrence qi hg first tail hv hn hs r Q q A T F Z input a b c base ht hu hj h
  dsimp only
  intro hA hT hF hZ hplans
  let p := resources query k occurrence qi hg first tail
  obtain ⟨hambient,hwidth,hd,hprecision,hjet⟩ :=
    produced_dimensions_le query k occurrence qi hg first tail hn hs
  have hbase : 0 < p.labelBase := by
    change 0 < 2*ambient query*matrixHeight query k+1
    omega
  have hheads : 1 ≤ p.heads := make_heads_pos query k occurrence _ _ _ _ _ _
  have hbits : 1 ≤ p.bits := make_bits_pos query k occurrence _ _ _ _ _ _
  have hb := he q A T F Z input p.bits k a b c p base h hA hT hF hZ hplans
    hambient (by simpa only [ht] using hwidth) hd (by simpa only [hu] using hprecision)
    (by simpa only [hj] using hjet)
    (by rw [hj]; exact (produced_order_eq query k occurrence qi hg first tail hv).le)
    hbase hheads hbits
  apply hb.trans
  have hp := Nat.pow_le_pow_left (produced_bits_succ_le query k occurrence qi hg first tail hn) ((b+5)*e)
  rw [←pow_mul] at hp
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
