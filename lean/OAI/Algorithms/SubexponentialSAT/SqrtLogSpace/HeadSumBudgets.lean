import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceParameters

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open FactorTableBudgets

/-- The boundary accommodates existing words, a regenerated ring cache and
any specialized dictionary returned by a factor. -/
def compactCap (A : ℕ) : ℕ := A+4*A+6+payloadEnvelope A

def sourceCap (A : ℕ) : ℕ :=
  1029*compactCap A+99+A+A*FactorTableProgram.literalRecordBound A (payloadEnvelope A)+1

def arithmeticCap (A : ℕ) : ℕ :=
  1+compactCap A+A+2*A*A+FactorEvaluationSpace.inputScale (2*A) A A A A A A A

/-- Includes the physical staging cap as well as every ordinary source scalar. -/
def tableScalarCap (A : ℕ) : ℕ := A+sourceCap A+1029*compactCap A+99

def callbackEnvelope (A : ℕ) : ℕ :=
  FactorAssignmentProgram.callbackScratch.length*(2*compactCap A+3)+
  128*compactCap A+200+tableEnvelope (tableScalarCap A)+
  2000*(arithmeticCap A)^3+14000000*(arithmeticCap A)^9

def bodyEnvelope (A : ℕ) : ℕ :=
  3040000*(FactorAssignmentProgram.entryScratch.length+A+2*A+A+A+A+
    compactCap A+callbackEnvelope A+1)^10

def prefixCap (A : ℕ) : ℕ := bodyEnvelope A+9*(A+1)+8

def iterationEnvelope (A : ℕ) : ℕ :=
  2*bodyEnvelope A+126*prefixCap A+54*A+286

theorem compact_le (A : ℕ) : A+1 ≤ compactCap A := by
  unfold compactCap
  omega

theorem cache_le (M A : ℕ) (hM : M ≤ A) : 4*M+6 ≤ compactCap A := by
  unfold compactCap
  omega

theorem capacity_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A) (ht : q.p.t ≤ A) (hd : d ≤ A) :
    FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ compactCap A := by
  have hp := payload_bound_le n q.u q.J q.p.t d A hn hu hJ ht hd
  change FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d ≤ _
  unfold compactCap
  omega

theorem source_capacity_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hn : n ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A) (ht : q.p.t ≤ A) (hd : d ≤ A) :
    1029*compactCap A+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤
        sourceCap A := by
  have hp := payload_bound_le n q.u q.J q.p.t d A hn hu hJ ht hd
  unfold sourceCap FactorTableProgram.literalRecordBound
  gcongr

theorem arithmetic_positive (A : ℕ) : 1 ≤ arithmeticCap A := by
  unfold arithmeticCap
  omega

theorem compact_le_arithmetic (A : ℕ) : compactCap A ≤ arithmeticCap A := by
  unfold arithmeticCap
  omega

theorem scalar_le_arithmetic (A : ℕ) : A ≤ arithmeticCap A := by
  unfold arithmeticCap
  omega

theorem degree_le_arithmetic (d t A : ℕ) (hd : d ≤ A) (ht : t ≤ A) :
    d*baseWidth 3 t ≤ arithmeticCap A := by
  have hm : d*(2*t) ≤ 2*A*A := by nlinarith
  simp only [RingProgram.ternary_baseWidth]
  unfold arithmeticCap
  omega

theorem input_scale_le (t d n u J k m L A : ℕ)
    (ht : t ≤ A) (hd : d ≤ A) (hn : n ≤ A) (hu : u ≤ A)
    (hJ : J ≤ A) (hk : k ≤ A) (hm : m ≤ A) (hL : L ≤ A) :
    FactorEvaluationSpace.inputScale (baseWidth 3 t) d n u J k m L ≤ arithmeticCap A := by
  have hscale : FactorEvaluationSpace.inputScale (baseWidth 3 t) d n u J k m L ≤
      FactorEvaluationSpace.inputScale (2*A) A A A A A A A := by
    unfold FactorEvaluationSpace.inputScale
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  unfold arithmeticCap
  omega

/-- The actual indexed hash rows and marked clause use the same chosen Z. -/
theorem arithmetic_caps {r Q n d : ℕ} (q : Factor.Spec r Q n d) (width A : ℕ)
    (ht : q.p.t ≤ A) (hd : d ≤ A) (hn : n ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hwidth : width ≤ A) (hrows : ∀ f (hf : f < q.rows.length), q.rows[f].length ≤ A)
    (hdigits : q.digits.length ≤ A) (hmark : q.markedClause.length ≤ A)
    (hbit : q.bitWidth ≤ A) :
    1 ≤ arithmeticCap A ∧ compactCap A ≤ arithmeticCap A ∧
    q.bitWidth ≤ arithmeticCap A ∧ d*baseWidth 3 q.p.t ≤ arithmeticCap A ∧
    (∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ arithmeticCap A) ∧
    FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ arithmeticCap A := by
  exact ⟨arithmetic_positive A,compact_le_arithmetic A,
    hbit.trans (scalar_le_arithmetic A),degree_le_arithmetic d q.p.t A hd ht,
    fun f hf => input_scale_le _ _ _ _ _ _ _ _ _ ht hd hn hu hJ hwidth (hrows f hf) hdigits,
    input_scale_le _ _ _ _ _ _ _ _ _ ht hd hn hu hJ hmark (Nat.zero_le A) (Nat.zero_le A)⟩

private theorem table_scalar_caps (A : ℕ) :
    A ≤ tableScalarCap A ∧ sourceCap A ≤ tableScalarCap A ∧
    1029*compactCap A+99 ≤ tableScalarCap A ∧ compactCap A ≤ tableScalarCap A := by
  unfold tableScalarCap
  omega

theorem table_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hd : d ≤ A) (hn : n ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (ha : q.p.aWord.length ≤ A) (hw : q.p.width.length ≤ A)
    (hp : RowSelectionProgram.pairLength q.p.power ≤ A) :
    FactorAssignmentCallback.tableBudget q (compactCap A) (sourceCap A) ≤
      tableEnvelope (tableScalarCap A) := by
  obtain ⟨hA,hS,hH,hP⟩ := table_scalar_caps A
  have hl := literal_work_le q.p q.u q.J n (sourceCap A) (1029*compactCap A+99)
    (tableScalarCap A) (hu.trans hA) (hJ.trans hA) (hn.trans hA) hS hH
    (hr.trans hA) (hQ.trans hA) (hd.trans hA) (ht.trans hA) (hR.trans hA)
    (ha.trans hA) (hw.trans hA) (hp.trans hA)
  have hb := payload_bound_le n q.u q.J q.p.t d (tableScalarCap A)
    (hn.trans hA) (hu.trans hA) (hJ.trans hA) (ht.trans hA) (hd.trans hA)
  have hn' := hn.trans hA
  unfold FactorAssignmentCallback.tableBudget tableEnvelope
  gcongr

theorem callback_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hd : d ≤ A) (hn : n ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (ha : q.p.aWord.length ≤ A) (hw : q.p.width.length ≤ A)
    (hp : RowSelectionProgram.pairLength q.p.power ≤ A) :
    FactorAssignmentCallback.uniformCallbackBudget q (compactCap A) (sourceCap A)
      (arithmeticCap A) ≤ callbackEnvelope A := by
  have hb := table_budget_le q A hr hQ hd hn ht hR hu hJ ha hw hp
  unfold FactorAssignmentCallback.uniformCallbackBudget callbackEnvelope
  omega

theorem body_budget_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hd : d ≤ A) (hn : n ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (ha : q.p.aWord.length ≤ A) (hw : q.p.width.length ≤ A)
    (hp : RowSelectionProgram.pairLength q.p.power ≤ A) :
    896*compactCap A+HeadEvaluationProgram.StagedGate.bodyPolynomial (compactCap A)+
      HeadAcceptedCorrect.budget q (compactCap A) (sourceCap A) (arithmeticCap A) ≤
        bodyEnvelope A := by
  apply (HeadAcceptedCorrect.body_envelope_polynomial q (compactCap A) (sourceCap A)
    (arithmeticCap A)).trans
  have hc := callback_budget_le q A hr hQ hd hn ht hR hu hJ ha hw hp
  unfold bodyEnvelope
  simp only [RingProgram.ternary_baseWidth]
  gcongr

theorem counter_le (h A : ℕ) (hh : h ≤ A) : 9*(h+1)+8 ≤ prefixCap A := by
  unfold prefixCap
  omega

theorem head_iteration_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (h A : ℕ)
    (hr : r ≤ A) (hQ : Q ≤ A) (hd : d ≤ A) (hn : n ≤ A)
    (ht : q.p.t ≤ A) (hR : q.p.R ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (ha : q.p.aWord.length ≤ A) (hw : q.p.width.length ≤ A)
    (hp : RowSelectionProgram.pairLength q.p.power ≤ A) (hh : h ≤ A) :
    (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial (compactCap A)+
      HeadAcceptedCorrect.budget q (compactCap A) (sourceCap A) (arithmeticCap A))+
      126*prefixCap A+54*h+286)*2^h ≤ iterationEnvelope A*2^h := by
  have hb := body_budget_le q A hr hQ hd hn ht hR hu hJ ha hw hp
  apply Nat.mul_le_mul_right
  unfold iterationEnvelope
  omega

private theorem ordinary_comp {f g : ℕ → ℕ} (hf : Ordinary f) (hg : Ordinary g) :
    Ordinary (fun A => g (f A)) := by
  obtain ⟨C,e,hf⟩ := hf
  obtain ⟨K,d,hg⟩ := hg
  refine ⟨K*(C+1)^d,e*d,?_⟩
  intro A
  have h1 : 1 ≤ (A+1)^e := Nat.one_le_pow _ _ (by omega)
  have hb : f A+1 ≤ (C+1)*(A+1)^e := by
    have := hf A
    nlinarith
  calc
    _ ≤ K*(f A+1)^d := hg (f A)
    _ ≤ K*((C+1)*(A+1)^e)^d := by gcongr
    _ = _ := by rw [mul_pow,pow_mul]; ring

private theorem compact_ordinary : Ordinary compactCap := by
  unfold compactCap
  exact (ordinary_add (ordinary_add (ordinary_add ordinary_id (ordinary_mul (ordinary_const 4) ordinary_id)) (ordinary_const 6)) payloadEnvelope_polynomial)

private theorem source_ordinary : Ordinary sourceCap := by
  unfold sourceCap FactorTableProgram.literalRecordBound
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 1029) compact_ordinary) (ordinary_const 99)) ordinary_id) (ordinary_mul ordinary_id (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) (ordinary_mul (ordinary_const 2) payloadEnvelope_polynomial)) (ordinary_const 4)))) (ordinary_const 1))

private theorem arithmetic_ordinary : Ordinary arithmeticCap := by
  unfold arithmeticCap FactorEvaluationSpace.inputScale
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const 1) compact_ordinary) ordinary_id) (ordinary_mul (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id)) (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) ordinary_id) ordinary_id) ordinary_id) ordinary_id) ordinary_id) (ordinary_mul ordinary_id ordinary_id)) ordinary_id) ordinary_id) ordinary_id) (ordinary_const 1)))

private theorem table_scalar_ordinary : Ordinary tableScalarCap := by
  unfold tableScalarCap
  exact (ordinary_add (ordinary_add (ordinary_add ordinary_id source_ordinary) (ordinary_mul (ordinary_const 1029) compact_ordinary)) (ordinary_const 99))

private theorem callback_ordinary : Ordinary callbackEnvelope := by
  unfold callbackEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const FactorAssignmentProgram.callbackScratch.length) (ordinary_add (ordinary_mul (ordinary_const 2) compact_ordinary) (ordinary_const 3))) (ordinary_mul (ordinary_const 128) compact_ordinary)) (ordinary_const 200)) (ordinary_comp table_scalar_ordinary tableEnvelope_polynomial)) (ordinary_mul (ordinary_const 2000) (ordinary_pow arithmetic_ordinary 3))) (ordinary_mul (ordinary_const 14000000) (ordinary_pow arithmetic_ordinary 9)))

private theorem body_ordinary : Ordinary bodyEnvelope := by
  unfold bodyEnvelope
  exact (ordinary_mul (ordinary_const 3040000) (ordinary_pow (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_add (ordinary_const FactorAssignmentProgram.entryScratch.length) ordinary_id) (ordinary_mul (ordinary_const 2) ordinary_id)) ordinary_id) ordinary_id) ordinary_id) compact_ordinary) callback_ordinary) (ordinary_const 1)) 10))

private theorem prefix_ordinary : Ordinary prefixCap := by
  unfold prefixCap
  exact (ordinary_add (ordinary_add body_ordinary (ordinary_mul (ordinary_const 9) (ordinary_add ordinary_id (ordinary_const 1)))) (ordinary_const 8))

private theorem iteration_ordinary : Ordinary iterationEnvelope := by
  unfold iterationEnvelope
  exact (ordinary_add (ordinary_add (ordinary_add (ordinary_mul (ordinary_const 2) body_ordinary) (ordinary_mul (ordinary_const 126) prefix_ordinary)) (ordinary_mul (ordinary_const 54) ordinary_id)) (ordinary_const 286))

/-- All chosen capacities and the per-assignment time coefficient have fixed
polynomial growth. The constants precede the physical input cap. -/
theorem caps_polynomial : ∃ C e : ℕ, ∀ A,
    compactCap A ≤ C*(A+1)^e ∧ sourceCap A ≤ C*(A+1)^e ∧
    arithmeticCap A ≤ C*(A+1)^e ∧ prefixCap A ≤ C*(A+1)^e ∧
    iterationEnvelope A ≤ C*(A+1)^e := by
  obtain ⟨C,e,h⟩ := ordinary_add (ordinary_add (ordinary_add
    (ordinary_add compact_ordinary source_ordinary) arithmetic_ordinary) prefix_ordinary)
      iteration_ordinary
  refine ⟨C,e,fun A => ?_⟩
  have hs := h A
  dsimp only at hs
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

section ProducedWords
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram
open LeafHeadSetupProgram.Native LeafParametersProgram

variable (query : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (query.input k))
variable (first : Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q)
variable (tail : List (Word (LeafProgram.Query.packingProblem query k hg).r
    (LeafProgram.Query.packingProblem query k hg).Q))
variable (node : Fin (LeafProgram.Query.packingProblem query k hg).Q)

local notation "s" => queryInputsAddressed query k hg first tail node

/-- The actual addressed constructor uses canonical polynomial-width word(s).
The denominator value may be exponential; only its physical binary length
appears in this statement. No arbitrary padding premise is required. -/
theorem addressed_source_word_caps (S : ℕ) (hQ : (s).Q ≤ S) (hR : (s).R ≤ S) :
    (s).height.length ≤ S ∧ RowSelectionProgram.pairLength (s).power ≤ S+1 ∧
    (s).width.length ≤ 1+2*S*S+S := by
  have hh := (s).height_le.trans hQ
  have hp : RowSelectionProgram.pairLength (s).power = (s).R-1+1 := by
    simp [RowSelectionProgram.pairLength,Inputs.power,IntegerCache.denominatorWord]
  have hw : (s).width.length = 1+2*(s).height.length*(s).R+(s).Q := by
    simp [queryInputsAddressed,queryInputs,LeafHeadSetupProgram.unary,
      LeafProgram.Query.packingProblem]
  refine ⟨hh,by omega,?_⟩
  rw [hw]
  gcongr

/-- These are the very source parameters built from the produced ring and
addressed query input. The bound follows the constructor's physical word(s). -/
theorem produced_source_word_caps
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (s).height (LeafHeadSetupProgram.unary (s).R)
      (s).width words)
    (m : Circuit.Model) (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (half : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache half e)
    (hfield : (s).Q < 3^(m.val 34))
    (S : ℕ) (hQ : (s).Q ≤ S) (hR : (s).R ≤ S) :
    let p := SourceBank.Parameters.ofProduced s words hc m ht hd M cache half e hp hfield
    p.aWord.length ≤ 4*(S+1)^2 ∧
    RowSelectionProgram.pairLength p.power ≤ 4*(S+1)^2 ∧
    p.width.length ≤ 4*(S+1)^2 := by
  obtain ⟨ha,hp,hw⟩ := addressed_source_word_caps query k hg first tail node S hQ hR
  change (s).height.length ≤ 4*(S+1)^2 ∧
    RowSelectionProgram.pairLength (s).power ≤ 4*(S+1)^2 ∧
    (s).width.length ≤ 4*(S+1)^2
  exact ⟨by nlinarith,by nlinarith,by nlinarith⟩

end ProducedWords

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
