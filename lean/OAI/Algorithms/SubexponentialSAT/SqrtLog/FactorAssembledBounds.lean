import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceAssignment
import OAI.Algorithms.SubexponentialSAT.SqrtLog.FactorResourceCapacity

namespace OAI.Algorithms

/-! Measured factor/assignment costs in assembled-work units. The remaining
physical hypotheses are on the bounded reference state and parser, never on
arbitrary untouched collector tapes. Padding is an explicit input factor. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly

/-- A complete incidence table has polynomial size in the ambient dimensions.
Sparse intermediate dictionaries are bounded separately by assembled work. -/
theorem incidenceTable_le (n J d B V : ℕ) (hn : n ≤ V) (hJ : J ≤ V)
    (hd : d ≤ V) (hB : B ≤ V) :
    n*literalRecordBound n (incidenceBitsBound n J (d*B)) ≤ 100*(V+1)^5 := by
  have hdiag : n*literalRecordBound n (incidenceBitsBound n J (d*B)) ≤
      V*literalRecordBound V (incidenceBitsBound V V (V*V)) := by
    unfold literalRecordBound incidenceBitsBound
    gcongr
  have hp (j : ℕ) (hj : j ≤ 5) : V^j ≤ (V+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ V) j).trans (Nat.pow_le_pow_right (by omega) hj)
  have h1 : V ≤ (V+1)^5 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  apply hdiag.trans
  unfold literalRecordBound incidenceBitsBound
  nlinarith

/-- This envelope permits all base words and parser tails to depend on a
fixed power of assembled work. It makes no input-polynomial claim for them. -/
def physicalEnvelope (U V W : ℕ) : ℕ := 100*(U+1)*(V+1)^5*(W+1)

theorem physicalEnvelope_bounds (U V W : ℕ) :
    U ≤ physicalEnvelope U V W ∧ 2*U ≤ physicalEnvelope U V W ∧
    V ≤ physicalEnvelope U V W ∧ V*V ≤ physicalEnvelope U V W ∧
    100*(V+1)^5 ≤ physicalEnvelope U V W ∧
    10*(V+1)^4*(W+1) ≤ physicalEnvelope U V W := by
  have h5 : 1 ≤ (V+1)^5 := Nat.one_le_pow _ _ (by omega)
  have hv : V+1 ≤ (V+1)^5 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ V+1) (show 1 ≤ 5 by decide)
  have hvv : V*V ≤ (V+1)^5 := by
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ V+1) (show 2 ≤ 5 by decide)
    nlinarith
  have h4 : (V+1)^4 ≤ (V+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hU : 2*U ≤ physicalEnvelope U V W := by
    unfold physicalEnvelope
    calc
      2*U = (2*U)*1*1 := by ring
      _ ≤ (100*(U+1))*(V+1)^5*(W+1) := by gcongr <;> omega
  have hV : 100*(V+1)^5 ≤ physicalEnvelope U V W := by
    unfold physicalEnvelope
    calc
      _ = 100*1*(V+1)^5*1 := by ring
      _ ≤ _ := by gcongr <;> omega
  refine ⟨by omega,hU,by omega,by omega,hV,?_⟩
  unfold physicalEnvelope
  gcongr ; omega

theorem payloadBound_le_base {r Q n d : ℕ} {q : Factor.Spec r Q n d} {S A : ℕ}
    {base : Fin 768 → List Bool} (h : FactorReady.Input q S A base) :
    FactorReady.payloadBound q.rawRows q.clauses ≤ 2*A := by
  have hr := h.size 701
  have hc := h.size 700
  rw [h.rows] at hr
  rw [h.clauses] at hc
  have hp := payloadBound_le_inputs q.rawRows q.clauses
  omega

/-- The independent source-size and sparse-byte hypotheses have disappeared:
source size comes from actual physical words; Good bytes come from support
capacity. The residual bounds are exactly the producer-to-reference-state
interface. All constants precede all queries, caps and resource records. -/
theorem assignmentCost_resource_polynomial : ∃ C e : ℕ, ∀ {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (A T F Z U V k : ℕ) (p : CostAssembly.Resources)
    (base : Fin 768 → List Bool),
    FactorReady.Input q (sourceCap q A T F) A base →
    A ≤ U → T ≤ U → F ≤ U → Z ≤ U →
    (LayoutOwnerFiberProgram.stream q.ps).length ≤ U →
    n ≤ V → baseWidth 3 q.p.t ≤ V → d ≤ V → q.u ≤ V → q.J ≤ V →
    q.J ≤ CostAssembly.jetOrder k n p →
    0 < p.labelBase → 1 ≤ p.heads → 1 ≤ p.bits →
    assignmentCost q A T F Z ≤ C*(physicalEnvelope U V (CostAssembly.assembledWork k n p)+1)^e := by
  obtain ⟨C,e,he⟩ := assignmentCost_polynomial
  refine ⟨C,e,?_⟩
  intro r Q n d q A T F Z U V k p base h hA hT hF hZ hplans hn hB hd hu hJ horder hbase hheads hbits
  obtain ⟨hU,h2U,hV,hVV,h100,h10⟩ := physicalEnvelope_bounds U V (CostAssembly.assembledWork k n p)
  apply he q A T F Z _ base h (hA.trans hU) (hT.trans hU) (hF.trans hU) (hZ.trans hU)
    (hn.trans hV) (hJ.trans hV)
  · exact (Nat.mul_le_mul hd hB).trans hVV
  · exact (seedBound_le_work k n _ d q.u q.J V p horder hbase hheads hbits hn hB hd hu hJ).trans h10
  · exact (payloadBound_le_base h).trans ((Nat.mul_le_mul_left 2 hA).trans h2U)
  · exact (incidenceTable_le n q.J d _ V hn hJ hd hB).trans h100
  · exact hplans.trans hU

/-- Padding contributes its actual input length, and is not silently replaced
by the ambient variable count. The exponents on work are fixed constants. -/
def paddingEnvelope (input V W a b c : ℕ) : ℕ :=
  (input+1)^a*(V+1)^b*(W+1)^c

theorem physicalEnvelope_padding_le (input V W a b c : ℕ) :
    physicalEnvelope (paddingEnvelope input V W a b c) V W+1 ≤
      201*(input+1)^a*(V+1)^(b+5)*(W+1)^(c+1) := by
  have hp : 1 ≤ paddingEnvelope input V W a b c := by
    unfold paddingEnvelope
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
      (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (by omega))
  have hv : 1 ≤ (V+1)^5 := Nat.one_le_pow _ _ (by omega)
  have hw : 1 ≤ W+1 := by omega
  have hbig : 1 ≤ paddingEnvelope input V W a b c*(V+1)^5*(W+1) :=
    Nat.mul_le_mul (Nat.mul_le_mul hp hv) hw
  calc
    _ ≤ 201*paddingEnvelope input V W a b c*(V+1)^5*(W+1) := by
      unfold physicalEnvelope
      nlinarith
    _ = _ := by unfold paddingEnvelope; rw [pow_add,pow_add]; simp only [pow_one]; ring

/-- A direct substitution rule for the measured complete assignment budget.
No source-cost or evaluator-cost oracle is a premise. -/
theorem assignmentCost_padding_polynomial : ∃ C e : ℕ, ∀ {r Q n d : ℕ}
    (q : Factor.Spec r Q n d) (A T F Z input V k a b c : ℕ) (p : CostAssembly.Resources)
    (base : Fin 768 → List Bool),
    FactorReady.Input q (sourceCap q A T F) A base →
    A ≤ paddingEnvelope input V (CostAssembly.assembledWork k n p) a b c →
    T ≤ paddingEnvelope input V (CostAssembly.assembledWork k n p) a b c →
    F ≤ paddingEnvelope input V (CostAssembly.assembledWork k n p) a b c →
    Z ≤ paddingEnvelope input V (CostAssembly.assembledWork k n p) a b c →
    (LayoutOwnerFiberProgram.stream q.ps).length ≤ paddingEnvelope input V (CostAssembly.assembledWork k n p) a b c →
    n ≤ V → baseWidth 3 q.p.t ≤ V → d ≤ V → q.u ≤ V → q.J ≤ V →
    q.J ≤ CostAssembly.jetOrder k n p →
    0 < p.labelBase → 1 ≤ p.heads → 1 ≤ p.bits →
    assignmentCost q A T F Z ≤ C*(input+1)^(a*e)*(V+1)^((b+5)*e)*
      (CostAssembly.assembledWork k n p+1)^((c+1)*e) := by
  obtain ⟨C,e,he⟩ := assignmentCost_resource_polynomial
  refine ⟨C*201^e,e,?_⟩
  intro r Q n d q A T F Z input V k a b c p base h hA hT hF hZ hplans hn hB hd hu hJ horder hbase hheads hbits
  have hb := he q A T F Z _ V k p base h hA hT hF hZ hplans hn hB hd hu hJ horder hbase hheads hbits
  apply hb.trans
  calc
    _ ≤ C*(201*(input+1)^a*(V+1)^(b+5)*(CostAssembly.assembledWork k n p+1)^(c+1))^e := by
      exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (physicalEnvelope_padding_le input V _ a b c) e)
    _ = _ := by simp only [mul_pow,←pow_mul]; ring

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
