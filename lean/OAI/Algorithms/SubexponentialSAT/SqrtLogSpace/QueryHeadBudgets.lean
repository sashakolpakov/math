import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeColumns

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

/-- Includes the actual column-length bound obtained from the stored source. -/
def sourceSize (A : ℕ) : ℕ := (A+1)*(100*(A+2)^2+2)+A+1

def scalarCap (A : ℕ) : ℕ := 1000100*(sourceSize A+1)^10

def compact (A : ℕ) : ℕ := compactCap (scalarCap A)
def source (A : ℕ) : ℕ := sourceCap (scalarCap A)
def arithmetic (A : ℕ) : ℕ := arithmeticCap (scalarCap A)
def transient (A : ℕ) : ℕ := prefixCap (scalarCap A)

private theorem sourceSize_large (A : ℕ) : A+1 ≤ sourceSize A := by
  unfold sourceSize
  omega

private theorem scalarCap_large (A : ℕ) : sourceSize A+1 ≤ scalarCap A := by
  have h : sourceSize A+1 ≤ (sourceSize A+1)^10 := Nat.le_self_pow (by decide) _
  unfold scalarCap
  omega

theorem original_le_scalar (A : ℕ) : A+1 ≤ scalarCap A := by
  have h1 := sourceSize_large A
  have h2 := scalarCap_large A
  omega

private theorem load_envelope_le {n N D C L U : ℕ} (hU : 1 ≤ U)
    (hn : n ≤ U) (hN : N ≤ U) (hD : D ≤ U) (hC : C ≤ U) (hL : L ≤ U) :
    SignatureHeadLoader.retainedOutputBound n N D C L ≤ 41*U^3 := by
  have hm := QueryVisitorLoadBounds.matrixBound_le_monomial hU hn hD hC hL
  have h2 : U ≤ U^2 := Nat.le_self_pow (by decide) _
  have h3 : U^2 ≤ U^3 := Nat.pow_le_pow_right hU (by decide)
  have h13 : 1 ≤ U^3 := Nat.one_le_pow _ _ hU
  have hleft : n*(2*n+2) ≤ 4*U^2 := by
    calc
      _ ≤ U*(2*U+2) := by gcongr
      _ ≤ _ := by nlinarith
  have hright : (2*N+2)*N ≤ 4*U^2 := by
    calc
      _ ≤ (2*U+2)*U := by gcongr
      _ ≤ _ := by nlinarith
  unfold SignatureHeadLoader.retainedOutputBound
  change n*(2*n+2)+2+(2*N+2)*N+QueryVisitorLoadBounds.matrixBound n D C L ≤ _
  omega

/-- Physical master words derive the column, full matrix, full key and loader
output bounds. No column evaluator or successful layout run is assumed. -/
theorem loader_caps (s : Native.Inputs) (a : Data) (A L : ℕ)
    (ha : Native.Ready s a) (hbound : WordBound A a) (hL : L ≤ A) :
    SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L ≤ scalarCap A ∧
    QueryVisitorLoadBounds.matrixEnvelope s L ≤ scalarCap A ∧
    QueryVisitorLoadBounds.keyEnvelope s L ≤ scalarCap A ∧
    11*s.n+6 ≤ scalarCap A := by
  have hi := NodeTime.inputBounds s a ha A hbound
  have hc := (NodeTime.columns_le hi).2
  have hN : s.N ≤ A := by simpa [ha.factors,unary] using hbound 129
  let U := sourceSize A+1
  have hAU : A+1 ≤ U := by dsimp [U]; have := sourceSize_large A; omega
  have hU : 1 ≤ U := by omega
  have hn : s.n ≤ U := by have := hi.n; omega
  have hN' : s.N ≤ U := by omega
  have hD : s.D ≤ U := by have := hi.D; omega
  have hC : s.columnLength ≤ U := by dsimp [U,sourceSize]; omega
  have hL' : L ≤ U := by omega
  have hl := load_envelope_le hU hn hN' hD hC hL'
  have hm := QueryVisitorLoadBounds.matrixEnvelope_le_monomial s hU hn hD hC hL'
  have hk := QueryVisitorLoadBounds.keyEnvelope_le_monomial s hU hn hD hC hL'
  have h3 : U^3 ≤ U^10 := Nat.pow_le_pow_right hU (by decide)
  have h1 : U ≤ U^10 := Nat.le_self_pow (by decide) _
  have h0 : 1 ≤ U^10 := Nat.one_le_pow _ _ hU
  change _ ≤ 1000100*U^10 ∧ _ ≤ 1000100*U^10 ∧ _ ≤ 1000100*U^10 ∧ _ ≤ 1000100*U^10
  exact ⟨by omega,by omega,by omega,by omega⟩

/-- Every numerical field consumed by the fixed head evaluator is now
constructed from the actual native master state and actual source identities.
Only the mathematical radius and clause-width properties remain source facts. -/
theorem headBounds (s : Native.Inputs) {d : ℕ} (q : Factor.Spec s.r s.Q s.n d)
    (a : Data) (A L M width : ℕ) (ha : Native.Ready s a) (hbound : WordBound A a)
    (hL : L ≤ A) (hM : M ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A)
    (hu : q.u ≤ A) (hJ : q.J ≤ A) (hbit : q.bitWidth ≤ A)
    (hwidth : width ≤ A) (hrows : ∀ f (hf : f < q.rows.length), q.rows[f].length ≤ A)
    (hmark : q.markedClause.length ≤ A)
    (hR : q.p.R = s.R) (hword : q.p.width = s.width) (hpower : q.p.power = s.power)
    (hdimension : q.ps.length = s.D) (hradius : q.p.R+1 ≤ s.Q)
    (hclauses : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width) :
    QueryVisitorHead.HeadBounds s q M (compact A) (source A) (arithmetic A)
      (transient A) L width := by
  let T := scalarCap A
  have hAT : A+1 ≤ T := original_le_scalar A
  have hA : A ≤ T := by omega
  have hi := NodeTime.inputBounds s a ha A hbound
  have hr := hi.r.trans hA
  have hQ := hi.Q.trans hA
  have hn := hi.n.trans hA
  have hd' := hd.trans hA
  have ht' := ht.trans hA
  have hu' := hu.trans hA
  have hJ' := hJ.trans hA
  have hR' : q.p.R ≤ T := hR ▸ hi.R.trans hA
  have ha' : q.p.aWord.length ≤ T := q.p.hAQ.trans hQ
  have hw' : q.p.width.length ≤ T := hword ▸ hi.width.trans hA
  have hp' : RowSelectionProgram.pairLength q.p.power ≤ T := by
    rw [hpower]
    simp only [RowSelectionProgram.pairLength,Native.Inputs.power,
      LayoutProgram.IntegerCache.denominatorWord,List.length_append,List.length_replicate,
      List.length_singleton,List.length_nil,Nat.add_zero]
    have := hi.R
    omega
  have hcompact : T+1 ≤ compactCap T := compact_le T
  obtain ⟨hl,hm,hk,hs⟩ := loader_caps s a A L ha hbound hL
  have hcapacity := capacity_le q T hn hu' hJ' ht' hd'
  have hproduct := payload_bound_le s.n q.p.t q.J q.p.t d T hn ht' hJ' ht' hd'
  have hsize := source_capacity_le q T hn hu' hJ' ht' hd'
  have hdigits : q.digits.length ≤ T := by simpa [Factor.Spec.digits] using ht'
  obtain ⟨hz,hpz,hbz,hdz,hhz,hmz⟩ := arithmetic_caps q width T ht' hd' hn hu' hJ'
    (hwidth.trans hA) (fun f hf => (hrows f hf).trans hA) hdigits
    (hmark.trans hA) (hbit.trans hA)
  have hlocal := body_budget_le q T hr hQ hd' hn ht' hR' hu' hJ' ha' hw' hp'
  refine ⟨?_,?_,?_,?_,?_,?_,?_,hcapacity,?_,hsize,hradius,hclauses,
    hz,hpz,hbz,hdz,hhz,hmz,?_,?_⟩
  · change _ ≤ compactCap T
    omega
  · change _ ≤ compactCap T
    omega
  · change _ ≤ compactCap T
    omega
  · change _ ≤ compactCap T
    omega
  · change _ ≤ compactCap T
    omega
  · change _ ≤ compactCap T
    rw [hdimension]
    have := hi.D
    omega
  · exact cache_le M T (hM.trans hA)
  · change FactorTableNative.specializedPayloadBound s.n q.p.t q.J (baseWidth 3 q.p.t) d ≤ compactCap T
    unfold compactCap
    omega
  · change 896*compactCap T+HeadEvaluationProgram.StagedGate.bodyPolynomial (compactCap T)+
      HeadAcceptedCorrect.budget q (compactCap T) (sourceCap T) (arithmeticCap T) ≤ prefixCap T
    unfold prefixCap
    omega
  · exact counter_le s.n T hn

/-- Existing retained stacks use the compact boundary; transient space is
never fed back into the next call's input allowance. -/
theorem incoming_bound {r s : ℕ} (a : StructuredProgram.State r s) (A : ℕ)
    (ha : WordBound A a) : WordBound (compact A) a := by
  intro i
  apply (ha i).trans
  have h := original_le_scalar A
  have hp := compact_le (scalarCap A)
  change A ≤ compactCap (scalarCap A)
  omega

private theorem scalar_ordinary : OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial.Ordinary scalarCap := by
  unfold scalarCap sourceSize
  exact (ordinary_mul (ordinary_const 1000100) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_add ordinary_id (ordinary_const 1)) (ordinary_add (ordinary_mul (ordinary_const 100) (ordinary_pow (ordinary_add ordinary_id (ordinary_const 2)) 2)) (ordinary_const 2))) ordinary_id) (ordinary_const 1)) (ordinary_const 1)) 10))

/-- Constants are fixed before the original physical/scalar allowance. All
four actual capacities and the sharp per-head exponential coefficient use
this same ordinary polynomial; the factor2^h remains separate. -/
theorem caps_polynomial : ∃ C e : ℕ, ∀ A,
    compact A ≤ C*(A+1)^e ∧ source A ≤ C*(A+1)^e ∧
    arithmetic A ≤ C*(A+1)^e ∧ transient A ≤ C*(A+1)^e ∧
    HeadSumBudgets.iterationEnvelope (scalarCap A) ≤ C*(A+1)^e := by
  obtain ⟨K,f,hscalar⟩ := scalar_ordinary
  obtain ⟨C,e,hcaps⟩ := HeadSumBudgets.caps_polynomial
  refine ⟨C*(K+1)^e,f*e,fun A => ?_⟩
  have h1 : 1 ≤ (A+1)^f := Nat.one_le_pow _ _ (by omega)
  have hb : scalarCap A+1 ≤ (K+1)*(A+1)^f := by
    have := hscalar A
    nlinarith
  have hpoly : C*(scalarCap A+1)^e ≤ (C*(K+1)^e)*(A+1)^(f*e) := by
    calc
      _ ≤ C*((K+1)*(A+1)^f)^e := by gcongr
      _ = _ := by rw [mul_pow,pow_mul]; ring
  obtain ⟨hp,hs,hz,hb,ht⟩ := hcaps (scalarCap A)
  exact ⟨hp.trans hpoly,hs.trans hpoly,hz.trans hpoly,hb.trans hpoly,ht.trans hpoly⟩

/-- Actual post-head multiplication, including all dictionary arithmetic. -/
def multiplyEnvelope (A : ℕ) : ℕ :=
  51000*(compact A+1)+4000000*(6*A+1)^10

/-- Covers the complete visitor's polynomial time coefficient and its
all-prefix max bound, including load, preparation, head scan and multiplication. -/
def visitorEnvelope (A : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope A (compact A)+100*compact A+200+
    HeadSumBudgets.iterationEnvelope (scalarCap A)+multiplyEnvelope A+
    996*compact A+200+transient A+896*compact A

theorem multiply_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    QueryVisitorHead.multiplyBudget q (compact A) ≤ multiplyEnvelope A := by
  have h := FactorProductSpace.budget_polynomial n (baseWidth 3 q.p.t) d q.p.t q.J
  have hscale : n+baseWidth 3 q.p.t+d+q.p.t+q.J+1 ≤ 6*A+1 := by
    simp only [RingProgram.ternary_baseWidth]
    omega
  unfold QueryVisitorHead.multiplyBudget multiplyEnvelope
  gcongr
  exact h.trans (by gcongr)

theorem visitor_time_coefficient_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hn : n ≤ A) (hd : d ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hw : q.p.width.length ≤ A) (hp : RowSelectionProgram.pairLength q.p.power ≤ A+1) :
    QueryVisitorHead.timeCoefficient q A (compact A) (source A) (arithmetic A)
      (transient A) ≤ visitorEnvelope A := by
  let T := scalarCap A
  have hAT := original_le_scalar A
  have hA : A ≤ T := by dsimp [T]; omega
  have hs := HeadSumBudgets.body_budget_le q T (hr.trans hA) (hQ.trans hA)
    (hd.trans hA) (hn.trans hA) (ht.trans hA) (hR.trans hA) (hu.trans hA) (hJ.trans hA)
    (q.p.hAQ.trans (hQ.trans hA)) (hw.trans hA) (hp.trans hAT)
  have hm := multiply_budget_le q A hn hd ht hJ
  have hn' := hn.trans hA
  unfold QueryVisitorHead.timeCoefficient visitorEnvelope HeadSumBudgets.iterationEnvelope
  change QueryVisitorLoad.runEnvelope A (compact A)+100*compact A+200+
    (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial (compactCap T)+
      HeadAcceptedCorrect.budget q (compactCap T) (sourceCap T) (arithmeticCap T))+
      126*prefixCap T+54*n+286)+QueryVisitorHead.multiplyBudget q (compact A) ≤
    QueryVisitorLoad.runEnvelope A (compact A)+100*compact A+200+
      (2*bodyEnvelope T+126*prefixCap T+54*T+286)+multiplyEnvelope A+
      996*compact A+200+transient A+896*compact A
  omega

theorem visitor_prefix_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    max (QueryVisitorLoad.runEnvelope A (compact A))
      (max (996*compact A+200)
        (max (transient A) (896*compact A+QueryVisitorHead.multiplyBudget q (compact A)))) ≤
      visitorEnvelope A := by
  have hm := multiply_budget_le q A hn hd ht hJ
  unfold visitorEnvelope
  exact max_le (by omega) (max_le (by omega) (max_le (by omega) (by omega)))

private theorem compact_ordinary : Ordinary compact := by
  obtain ⟨C,e,h⟩ := caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

private theorem transient_ordinary : Ordinary transient := by
  obtain ⟨C,e,h⟩ := caps_polynomial
  exact ⟨C,e,fun A => (h A).2.2.2.1⟩

private theorem iteration_ordinary :
    Ordinary (fun A => HeadSumBudgets.iterationEnvelope (scalarCap A)) := by
  obtain ⟨C,e,h⟩ := caps_polynomial
  exact ⟨C,e,fun A => (h A).2.2.2.2⟩

private theorem multiply_ordinary : Ordinary multiplyEnvelope := by
  unfold multiplyEnvelope
  exact (ordinary_add (ordinary_mul (ordinary_const 51000) (ordinary_add compact_ordinary (ordinary_const 1))) (ordinary_mul (ordinary_const 4000000) (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 6) ordinary_id) (ordinary_const 1)) 10)))

/-- The complete actual one-head visitor has fixed polynomial overhead.
It is multiplied by the proved head-size exponent only after this theorem. -/
theorem visitor_polynomial : ∃ C e : ℕ, ∀ A, visitorEnvelope A ≤ C*(A+1)^e := by
  change Ordinary visitorEnvelope
  unfold visitorEnvelope QueryVisitorLoad.runEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const (1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3))) (ordinary_pow (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 2)) 64)) (ordinary_mul (ordinary_const 100) compact_ordinary)) (ordinary_const 200)) iteration_ordinary) multiply_ordinary) (ordinary_mul (ordinary_const 996) compact_ordinary)) (ordinary_const 200)) transient_ordinary) (ordinary_mul (ordinary_const 896) compact_ordinary))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
