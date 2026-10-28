import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramNumeratorRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramRowCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgramDefinitions

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Native

theorem numerator_eval {r Q : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (t : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (s : Store) (regs : Fin 16 → Bool)
    (hinput : ∀ i, s (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (regs ∘ numeratorRegs) t u y [] [] ([],[])).stacks i) :
    ∃ n rf result,
      n ≤ LayoutProgram.Numerator.budget as.length R width.length (pairLength power) t u y + 1 ∧
      Eval numerator n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (Function.update s 253 result.1) 254 result.2⟩ : Data) ∧
      pairValue result = LayoutProgram.Numerator.value as.length R t u y ∧
      pairLength result ≤ R * LayoutProgramScalar.termGrowth
        (2*width.length+pairLength power) := by
  let c := LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as
  let start := LayoutProgram.Numerator.state c (regs ∘ numeratorRegs) t u y [] [] ([],[])
  obtain ⟨n,hn,rr,result,he,hval,hmass,hlength⟩ := LayoutProgram.Numerator.command_eval
    Hwords width power (regs ∘ numeratorRegs) as R t u y hlen hwords hvalues hp hpt hwidth hAQ hQ
  have hin : projectState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data) = start := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i; exact hinput i
  have he' : Eval LayoutProgram.Numerator.command n
      (projectState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data))
      (LayoutProgram.Numerator.state c rr t u y [] [] result) := by
    rw [hin]; exact he
  have hr := eval_liftCommand_from_state LayoutProgram.Numerator.command 23 50
    numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
    numeratorRegs_injective numeratorPorts_injective he'
  have hout : (LayoutProgram.Numerator.state c rr t u y [] [] result).stacks =
      Function.update (Function.update start.stacks 50 result.1) 51 result.2 := by
    funext i
    by_cases h50 : i = 50 <;> by_cases h51 : i = 51 <;>
      simp [LayoutProgram.Numerator.state,start,Function.update_apply,h50,h51]
  have hbase : Function.extend numeratorPorts start.stacks s = s := by
    have h := congrArg StructuredProgram.State.stacks
      (embedState_project numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
        numeratorRegs_injective numeratorPorts_injective)
    rw [hin] at h
    exact h
  have hs : (embedState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
      (LayoutProgram.Numerator.state c rr t u y [] [] result)).stacks =
      Function.update (Function.update s 253 result.1) 254 result.2 := by
    change Function.extend numeratorPorts _ s = _
    rw [hout,ProgramLinking.extend_update numeratorPorts_injective,
      ProgramLinking.extend_update numeratorPorts_injective,hbase]
    rfl
  have heq : embedState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
      (LayoutProgram.Numerator.state c rr t u y [] [] result) =
      (⟨(embedState numeratorRegs numeratorPorts (⟨regs,s⟩ : Data)
        (LayoutProgram.Numerator.state c rr t u y [] [] result)).regs,
        Function.update (Function.update s 253 result.1) 254 result.2⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hs
  rw [heq] at hr
  exact ⟨n+1,_,result,by omega,hr,hval,
    hlength.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _))⟩



def integerBits (R W P : ℕ) : ℕ := R * LayoutProgramScalar.termGrowth (2*W+P)

def callbackBudget (num bits t d : ℕ) : ℕ :=
  num + 1 + polynomialBudget bits t d + 2*bits + 6

theorem callback_eval {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (node : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (s : Store) (ready : CachedReady t a M cache zero one minusOne s)
    (hinv : s 252 = RingProgram.flat invDenom) (regs : Fin 16 → Bool)
    (hinput : ∀ i, s (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (regs ∘ numeratorRegs) node u y [] [] ([],[])).stacks i) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool) (out : ModelCode t d),
      n ≤ callbackBudget
        (LayoutProgram.Numerator.budget as.length R width.length (pairLength power) node u y)
        (integerBits R width.length (pairLength power)) t d ∧
      Eval callback n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update s 255 (RingProgram.flat out)⟩ : Data) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
          ((LayoutProgram.Numerator.value as.length R node u y : ℤ) : a.O t) := by
  have h253 : s 253 = [] := by
    simpa [numeratorPorts,LayoutProgram.Numerator.state] using hinput 50
  have h254 : s 254 = [] := by
    simpa [numeratorPorts,LayoutProgram.Numerator.state] using hinput 51
  obtain ⟨n1,r1,result,hn1,e1,hval,hlenResult⟩ := numerator_eval Hwords width power as R node
    u y hlen hwords hvalues hp hpt hwidth hAQ hQ s regs hinput
  let s1 := Function.update (Function.update s 253 result.1) 254 result.2
  let out := cachedScaledValue t a M cache zero one minusOne invDenom result.1 result.2
  let s2 := Function.update s1 255 (RingProgram.flat out)
  let s3 := Function.update s2 253 []
  have hr : CachedReady t a M cache zero one minusOne s1 := by
    apply cachedReady_frame t a M cache zero one minusOne s s1 ready
    intro i hi h1 h2
    simp [s1,h1,h2]
  have hri : s1 252 = RingProgram.flat invDenom := by simp [s1,hinv]
  obtain ⟨n2,r2,hn2,e2⟩ := cachedScaledCommand_run t a M cache hz
    zero one minusOne invDenom s1 hr hri r1
  have e2' : Eval modelScaledCommand n2 (⟨r1,s1⟩ : Data) (⟨r2,s2⟩ : Data) := by
    simpa [s2,out,s1] using e2
  have hb : modelScaledBudget (result.1.length+result.2.length) t d ≤
      polynomialBudget (integerBits R width.length (pairLength power)) t d := by
    apply (modelScaledBudget_polynomial _ _ _).trans
    unfold polynomialBudget
    have hsize : result.1.length+result.2.length ≤ integerBits R width.length (pairLength power) :=
      hlenResult
    gcongr
  have hn2' : n2 ≤ polynomialBudget (integerBits R width.length (pairLength power)) t d := by
    apply LE.le.trans hn2
    simpa [s1] using hb
  obtain ⟨n3,r3,hn3,e3⟩ := clear_run 253 s2 r2
  obtain ⟨n4,r4,hn4,e4⟩ := clear_run 254 s3 r3
  have hfinal : Function.update s3 254 [] = Function.update s 255 (RingProgram.flat out) := by
    funext i
    by_cases h1 : i = 253 <;> by_cases h2 : i = 254 <;> by_cases h3 : i = 255 <;>
      simp [s3,s2,s1,h1,h2,h3,h253,h254]
  rw [hfinal] at e4
  have hdecode : (RingProgram.modelRing t ht hd a M cache).decode out =
      -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        ((LayoutProgram.Numerator.value as.length R node u y : ℤ) : a.O t) := by
    let ops := RingProgram.modelRing t ht hd a M cache
    have hh := scaledValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
      (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
      zero one minusOne invDenom hzero hone hminus result.1 result.2
    change ops.decode out = _
    change ops.decode out = _ at hh
    rw [show ((BinaryArithmetic.toNat result.1 : ℤ) -
      (BinaryArithmetic.toNat result.2 : ℤ)) = LayoutProgram.Numerator.value as.length R node u y
        by exact hval] at hh
    exact hh
  refine ⟨n1+(n2+(n3+n4)),r4,out,?_,e1.seq (e2'.seq (e3.seq e4)),hdecode⟩
  have hn3' : n3 ≤ 2*result.1.length+3 := by simpa [s2,s1] using hn3
  have hn4' : n4 ≤ 2*result.2.length+3 := by simpa [s3,s2,s1] using hn4
  unfold callbackBudget
  change result.1.length+result.2.length ≤ integerBits R width.length (pairLength power) at hlenResult
  omega

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod


namespace Native

theorem state_node_update {r Q : ℕ} (c : LayoutProgram.Numerator.Saved)
    (regs : Fin 10 → Bool) (start node : Fin Q) (u y : UniversalType r Q 1) :
    (LayoutProgram.Numerator.state c regs node u y [] [] ([],[])).stacks =
      Function.update (LayoutProgram.Numerator.state c regs start u y [] [] ([],[])).stacks
        37 (List.replicate node.val true) := by
  funext i
  fin_cases i <;> rfl

theorem port_range (i : Fin 64) :
    (numeratorPorts i).val < 64 ∨ numeratorPorts i = 253 ∨ numeratorPorts i = 254 := by
  by_cases h50 : i = 50
  · simp [numeratorPorts,h50]
  · by_cases h51 : i = 51
    · simp [numeratorPorts,h51]
    · simp [numeratorPorts,h50,h51]

theorem loop_input {r Q : ℕ} (c : LayoutProgram.Numerator.Saved)
    (start node : Fin Q) (u y : UniversalType r Q 1) (base : Store)
    (hinput : ∀ i, base (numeratorPorts i) =
      (LayoutProgram.Numerator.state c (fun _ => false) start u y [] [] ([],[])).stacks i)
    (remaining acc : List Bool) (regs : Fin 16 → Bool) :
    ∀ i, (loopState base node.val remaining acc) (numeratorPorts i) =
      (LayoutProgram.Numerator.state c (regs ∘ numeratorRegs) node u y [] [] ([],[])).stacks i := by
  intro i
  have h64 : numeratorPorts i ≠ 64 := by
    have h := port_range i
    rcases h with h | h | h
    · intro he; rw [he] at h; norm_num at h
    · rw [h]; decide
    · rw [h]; decide
  have h65 : numeratorPorts i ≠ 65 := by
    have h := port_range i
    rcases h with h | h | h
    · intro he; rw [he] at h; norm_num at h
    · rw [h]; decide
    · rw [h]; decide
  by_cases hi : i = 37
  · subst i
    simp [loopState,numeratorPorts,LayoutProgram.Numerator.state,
      LayoutProgram.Numerator.baseStacks,LayoutProgram.Guard.guardInput]
  · have h37 : numeratorPorts i ≠ 37 := by
      intro he
      have hv := congrArg Fin.val he
      unfold numeratorPorts at hv
      split_ifs at hv <;> simp_all ; omega
    rw [loopState,Function.update_of_ne h65,Function.update_of_ne h64,
      Function.update_of_ne h37,hinput i]
    have he := congrFun (state_node_update c (regs ∘ numeratorRegs) start node u y) i
    simpa [Function.update_of_ne hi,LayoutProgram.Numerator.state] using he.symm

def numeratorBudget {r Q : ℕ} (A R W P : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  ∑ node : Fin Q, LayoutProgram.Numerator.budget A R W P node u y


def tableBudget {r Q : ℕ} (A R W P t d : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  Q * (callbackBudget (numeratorBudget A R W P u y) (integerBits R W P) t d +
    6 * (d * SubexpLiftRing.baseWidth 3 t) + 16) + 14

def ValidWord {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (u y : UniversalType r Q 1) (j : ℕ) (word : List Bool) : Prop :=
  ∃ hj : j < Q, ∃ out : ModelCode t d,
    word = RingProgram.flat out ∧
    (RingProgram.modelRing t ht hd a M cache).decode out =
      -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        ((LayoutProgram.Numerator.value A R ⟨j,hj⟩ u y : ℤ) : a.O t)

theorem callback_relation {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (start : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (base : Store) (ready : CachedReady t a M cache zero one minusOne base)
    (hinv : base 252 = RingProgram.flat invDenom)
    (hinput : ∀ i, base (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _ => false) start u y [] [] ([],[])).stacks i) :
    CallbackRelation callback base (ValidWord as.length R t ht hd a M cache invDenom u y)
      Q (callbackBudget (numeratorBudget as.length R width.length (pairLength power) u y)
        (integerBits R width.length (pairLength power)) t d) (d * SubexpLiftRing.baseWidth 3 t) := by
  intro j hj remaining acc regs
  let node : Fin Q := ⟨j,hj⟩
  let s := loopState base j remaining acc
  have hready : CachedReady t a M cache zero one minusOne s := by
    apply cachedReady_frame t a M cache zero one minusOne base s ready
    intro i hi h253 h254
    have h37 : i ≠ 37 := by intro h; subst i; norm_num at hi
    have h64 : i ≠ 64 := by intro h; subst i; norm_num at hi
    have h65 : i ≠ 65 := by intro h; subst i; norm_num at hi
    simp [s,loopState,h37,h64,h65]
  have hi : s 252 = RingProgram.flat invDenom := by simp [s,loopState,hinv]
  have hsource := loop_input
    (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
    start node u y base hinput remaining acc regs
  obtain ⟨n,rf,out,hn,he,hv⟩ := callback_eval Hwords width power as R node u y
    hlen hwords hvalues hp hpt hwidth hAQ hQ t ht hd a M cache hz
    zero one minusOne invDenom hzero hone hminus s hready hi regs hsource
  have hnum : LayoutProgram.Numerator.budget as.length R width.length (pairLength power) node u y ≤
      numeratorBudget as.length R width.length (pairLength power) u y := by
    unfold numeratorBudget
    exact Finset.single_le_sum
      (f := fun k : Fin Q => LayoutProgram.Numerator.budget as.length R width.length (pairLength power) k u y)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ node)
  refine ⟨n,rf,RingProgram.flat out,?_,RingProgram.flat_length out,?_,he⟩
  · unfold callbackBudget at *
    omega
  · exact ⟨hj,out,rfl,hv⟩

/-- The resulting table is produced by a fixed native program from metadata
and prepared arithmetic caches, with a decode witness at every node. -/
theorem tableProgram_runsIn {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (start : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (base : Store) (ready : CachedReady t a M cache zero one minusOne base)
    (hinv : base 252 = RingProgram.flat invDenom)
    (hinput : ∀ i, base (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _ => false) start u y [] [] ([],[])).stacks i)
    (hq : (base 22).length = Q) (h37 : base 37 = [])
    (h64 : base 64 = []) (h65 : base 65 = []) (h67 : base 67 = [])
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (rf : Fin 16 → Bool),
      words.length = Q ∧ (∀ word ∈ words, word.length = d * SubexpLiftRing.baseWidth 3 t) ∧
      List.Forall₂ (ValidWord as.length R t ht hd a M cache invDenom u y) (List.range' 0 Q) words ∧
      RunsIn tableProgram (tableBudget as.length R width.length (pairLength power) t d u y)
        ((⟨regs,base⟩ : Data).withPC (some tableProgram.entry))
        ((⟨rf,Function.update base 67 words.flatten⟩ : Data).withPC none) := by
  have hs := callback_relation Hwords width power as R start u y hlen hwords hvalues hp hpt
    hwidth hAQ hQ t ht hd a M cache hz zero one minusOne invDenom hzero hone hminus base ready hinv hinput
  exact program_relation callback base _ Q _ _ hs hq h37 h64 h65 h67 ready.clean.1 ready.output regs

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators

/-- Every truncated recurrence count is bounded by R; the two scanned counts
are bounded by Q. This expression is a fixed polynomial in A,R,Q,W,P. -/
def scalarAllowance (A R Q W P : ℕ) : ℕ :=
  14*R+7*A+15+(3*Q+4)+LayoutProgramScalar.FromCounts.binomialCost Q R W+
    (LayoutProgramScalar.numeratorPrepareCost R A W P+
      LayoutProgramScalar.numeratorFoldCost R W P+1)+4*(R*W)+6+1

theorem scalar_cost_le (A R Q W P n h : ℕ) (hn : n ≤ Q) (hh : h ≤ Q) :
    LayoutProgramScalar.FromCounts.totalCost A R n h W P ≤ scalarAllowance A R Q W P := by
  unfold LayoutProgramScalar.FromCounts.totalCost scalarAllowance
    LayoutProgramScalar.FromCounts.binomialCost LayoutProgramScalar.numeratorPrepareCost
    LayoutProgramScalar.numeratorFoldCost
  gcongr <;> omega

/-- guardStageCost and scanStageCost are explicit fixed polynomials too. -/
def numeratorAllowance (r Q A R W P : ℕ) : ℕ :=
  Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q +
    Subexp.MatrixEntryProgram.scanStageCost r Q 1 0 + 7*Q + scalarAllowance A R Q W P + 20

theorem numerator_cost_le {r Q : ℕ} (A R W P : ℕ) (node : Fin Q)
    (u y : UniversalType r Q 1) :
    LayoutProgram.Numerator.budget A R W P node u y ≤ numeratorAllowance r Q A R W P := by
  have hu := Subexp.MatrixEntryEvaluation.unchangedCount_le (0 : Fin 1) u y
  have hh := Subexp.MatrixEntryEvaluation.transposedCount_le (0 : Fin 1) u y
  have hs := scalar_cost_le A R Q W P
    (Subexp.MatrixScanProgram.unchangedCount (Subexp.MatrixEntryEvaluation.rows 0 u y)-1)
    (Subexp.MatrixScanProgram.transposedCount (Subexp.MatrixEntryEvaluation.rows 0 u y))
    (by omega) hh
  have hg : Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 node.val ≤
      Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q := by
    unfold Subexp.MatrixExtendedEntryProgram.guardStageCost
    gcongr
    exact node.isLt.le
  unfold LayoutProgram.Numerator.budget numeratorAllowance
  omega

theorem numeratorBudget_le {r Q : ℕ} (A R W P : ℕ) (u y : UniversalType r Q 1) :
    numeratorBudget A R W P u y ≤ Q * numeratorAllowance r Q A R W P := by
  unfold numeratorBudget
  calc
    _ ≤ ∑ _node : Fin Q, numeratorAllowance r Q A R W P := by
      exact Finset.sum_le_sum fun node _ => numerator_cost_le A R W P node u y
    _ = _ := by simp

/-- An explicit polynomial upper bound on the complete constructed table. -/
def polynomialBudget (r Q A R W P t d : ℕ) : ℕ :=
  Q * (callbackBudget (Q * numeratorAllowance r Q A R W P) (integerBits R W P) t d +
    6*(d*SubexpLiftRing.baseWidth 3 t)+16)+14

theorem tableBudget_polynomial {r Q : ℕ} (A R W P t d : ℕ)
    (u y : UniversalType r Q 1) :
    tableBudget A R W P t d u y ≤ polynomialBudget r Q A R W P t d := by
  unfold tableBudget polynomialBudget callbackBudget
  gcongr
  exact numeratorBudget_le A R W P u y

/-- Translate the relational loop certificate to the emitter's per-node
getD interface without assuming an input scalar table. -/
theorem generated_word_at {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (u y : UniversalType r Q 1) (words : List (List Bool)) (hlen : words.length = Q)
    (hvalid : List.Forall₂ (ValidWord A R t ht hd a M cache invDenom u y) (List.range' 0 Q) words)
    (node : Fin Q) :
    ∃ out : ModelCode t d, words.getD node.val [] = RingProgram.flat out ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
          ((LayoutProgram.Numerator.value A R node u y : ℤ) : a.O t) := by
  have hw : node.val < words.length := by simp [hlen]
  have h := hvalid.get (by simp) hw
  simp only [List.get_eq_getElem,List.getElem_range',Nat.zero_add,Nat.one_mul] at h
  obtain ⟨hj,out,he,hv⟩ := h
  refine ⟨out,?_,?_⟩
  · rw [List.getD_eq_getElem words [] hw]
    exact he
  · exact hv

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native


namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT MulticolorTypes SubexpSymbolicCost IntegerRingLiftProgram

theorem sourceValue_scaled {C O : Type*} [CommRing O] {r Q : ℕ}
    (ops : RepresentedRing C O) (integerWord : ℤ → C)
    (hinteger : ∀ z, ops.decode (integerWord z) = (z : O)) (invDenom : C)
    (A R : ℕ) (node : Fin Q) (u y : UniversalType r Q 1) :
    ops.decode (LayoutProgram.sourceValue ops.program integerWord invDenom A R u 0 y node) =
      -ops.decode invDenom * ((LayoutProgram.Numerator.value A R node u y : ℤ) : O) := by
  unfold LayoutProgram.sourceValue
  by_cases h : Subexp.MatrixExtendedEntryProgram.anchorValid (0 : Fin 1) node u y
  · rw [ite_eq_left ((Subexp.MatrixExtendedEntryProgram.anchorValid_iff_joint (0 : Fin 1) node u y).mp h)]
    simp [LayoutProgram.Numerator.value,h,
ops.neg_correct,ops.mul_correct,hinteger,neg_mul]
  · have hj : ¬(u ∈ joint node (y.head node) (0 : Fin 1) ∧ y ∈ joint node (y.head node) (0 : Fin 1)) :=
      fun hj => h ((Subexp.MatrixExtendedEntryProgram.anchorValid_iff_joint (0 : Fin 1) node u y).mpr hj)
    rw [ite_eq_right hj]
    simp [LayoutProgram.Numerator.value,h,
ops.zero_correct]

/-- The exact value premise required by LayoutProgram.emitSource_runsIn now
follows from a generated table and a decoder correct on fixed-width words. -/
theorem generated_source_value {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (integerWord : ℤ → ModelCode t d)
    (hinteger : ∀ z, (RingProgram.modelRing t ht hd a M cache).decode (integerWord z) = (z : a.O t))
    (decode : List Bool → a.O t)
    (hdecode : ∀ code : ModelCode t d,
      decode (RingProgram.flat code) = (RingProgram.modelRing t ht hd a M cache).decode code)
    (u y : UniversalType r Q 1) (words : List (List Bool)) (hlen : words.length = Q)
    (hvalid : List.Forall₂ (ValidWord A R t ht hd a M cache invDenom u y) (List.range' 0 Q) words)
    (node : Fin Q) :
    decode (words.getD node.val []) =
      (RingProgram.modelRing t ht hd a M cache).decode
        (LayoutProgram.sourceValue (RingProgram.modelRing t ht hd a M cache).program
          integerWord invDenom A R u 0 y node) := by
  obtain ⟨out,hw,hv⟩ := generated_word_at A R t ht hd a M cache invDenom u y words hlen hvalid node
  rw [hw,hdecode,hv,sourceValue_scaled _ integerWord hinteger]

/-- The generated byte table consists of actual model codes, in node order.
This witness can be passed to typed source-expression and row constructors. -/
theorem generated_codes {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (u y : UniversalType r Q 1) (words : List (List Bool)) (hlen : words.length = Q)
    (hvalid : List.Forall₂ (ValidWord A R t ht hd a M cache invDenom u y) (List.range' 0 Q) words) :
    ∃ codes : Fin Q → ModelCode t d,
      words = List.ofFn (fun node => RingProgram.flat (codes node)) ∧
      ∀ node, (RingProgram.modelRing t ht hd a M cache).decode (codes node) =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
          ((LayoutProgram.Numerator.value A R node u y : ℤ) : a.O t) := by
  classical
  choose codes hbytes hvalues using
    (fun node => generated_word_at A R t ht hd a M cache invDenom u y words hlen hvalid node)
  refine ⟨codes,?_,hvalues⟩
  apply List.ext_getElem (by simp [hlen])
  intro j hj hj'
  have h := hbytes ⟨j,by omega⟩
  rw [List.getD_eq_getElem words [] hj] at h
  simpa using h

/-- Typed source values obtained from the executed table, without a supplied
table or a free byte-decoding premise. -/
theorem generated_source_codes {r Q d : ℕ} (A R t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d)
    (integerWord : ℤ → ModelCode t d)
    (hinteger : ∀ z, (RingProgram.modelRing t ht hd a M cache).decode (integerWord z) = (z : a.O t))
    (u y : UniversalType r Q 1) (words : List (List Bool)) (hlen : words.length = Q)
    (hvalid : List.Forall₂ (ValidWord A R t ht hd a M cache invDenom u y) (List.range' 0 Q) words) :
    ∃ codes : Fin Q → ModelCode t d,
      words = List.ofFn (fun node => RingProgram.flat (codes node)) ∧
      ∀ node, (RingProgram.modelRing t ht hd a M cache).decode (codes node) =
        (RingProgram.modelRing t ht hd a M cache).decode
          (LayoutProgram.sourceValue (RingProgram.modelRing t ht hd a M cache).program
            integerWord invDenom A R u 0 y node) := by
  obtain ⟨codes,hwords,hvalues⟩ := generated_codes A R t ht hd a M cache invDenom u y words hlen hvalid
  refine ⟨codes,hwords,fun node => ?_⟩
  rw [hvalues,sourceValue_scaled _ integerWord hinteger]

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

end OAI.Algorithms
