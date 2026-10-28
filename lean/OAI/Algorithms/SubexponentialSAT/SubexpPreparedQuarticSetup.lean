import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuarticPrelude
import OAI.Algorithms.SubexponentialSAT.SubexpFlatLift
import OAI.Algorithms.SubexponentialSAT.SubexpNegationSetup
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticFlatNeg
import OAI.Algorithms.SubexponentialSAT.SubexpCanonicalWords
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationPayload

namespace OAI.Algorithms

/-!
# Preparation of the selected quartic ring by finite bit programs

The selected polynomial's four coefficient words are input bytes from the
polynomial-search stage. Their lift and negation, the prime-power modulus,
width shape, literal quartets, and minus-one word are all computed here.
Natural-number powers and quotient values occur only in specifications.
-/

namespace SubexponentialSAT.SubexpPreparedQuarticSetup

open BitProgram StructuredCalls SubexpPreparedSetupCalls SubexpPreparedQuarticPrelude
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime]

def modulus : SubexpPreparedQuartic.Modulus p μ :=
  ⟨modulusWord p μ, (modulusWord_length p μ).le, SubexpQuarticRing.modulusBits_value p μ⟩

def sourceModulus : SubexpPreparedQuartic.Modulus p 1 :=
  ⟨primeWord p, by simp [baseWidth], by simp⟩

def minusOne : Word (baseWidth p μ) :=
  ⟨SubexpNegationSetup.preparedConstant (widthWord p μ) (modulusWord p μ), by
    rw [SubexpNegationSetup.preparedConstant_length, widthWord_length]⟩

theorem minusOne_value : wordValue p μ (minusOne p μ) = -1 := by
  have hv : BinaryArithmetic.toNat (modulusWord p μ) = p ^ μ := (modulus p μ).value
  have hm : 0 < BinaryArithmetic.toNat (modulusWord p μ) := by
    rw [hv]
    exact pow_pos (Fact.out : p.Prime).pos μ
  have hc : BinaryArithmetic.toNat (modulusWord p μ) ≤ 2 ^ (widthWord p μ).length := by
    rw [hv, widthWord_length]
    exact modulus_le_width p μ
  have h := SubexpNegationSetup.preparedConstant_cast (widthWord p μ) (modulusWord p μ) hm hc
  rw [hv] at h
  exact h

def lifted (a : Quad (Word (baseWidth p 1))) : Quad (Word (baseWidth p μ)) :=
  (SubexpWordLift.liftQuadRun p μ (sourceModulus p) a).1

def reduction (a : Quad (Word (baseWidth p 1))) : Quad (Word (baseWidth p μ)) :=
  SubexpQuarticNegMachine.negateWords p μ (modulus p μ) (minusOne p μ) (lifted p μ a)

def flat {B : ℕ} (a : Quad (Word B)) : List Bool := SubexpQuarticFlatNeg.flat a

@[simp] theorem flat_length {B : ℕ} (a : Quad (Word B)) : (flat a).length = 4 * B :=
  SubexpQuarticFlatNeg.flat_length a

theorem lift_encode_eq_flat {B : ℕ} (a : Quad (Word B)) : SubexpFlatLift.encode a = flat a := by
  simp [SubexpFlatLift.encode, SubexpFlatLift.flatten, SubexpFlatLift.quadWords,
    flat, SubexpQuarticFlatNeg.flat, SubexpQuarticFlatNeg.wordLists,
    FourWordPrograms.flatWords, Quad.toFn]

/-- Specification of one source word already emitted by the polynomial
producer. This encoding is not an extra instruction of the setup program. -/
def selectedInputWord (z : ZMod p) : Word (baseWidth p 1) :=
  ⟨SubexpEnumerationPayload.scalarBits z, by
    simp [SubexpEnumerationPayload.scalarWidth, baseWidth]⟩

@[simp] theorem selectedInputWord_value (z : ZMod p) :
    SubexpWordLift.sourceValue p (selectedInputWord p z) = z := by
  change (BinaryArithmetic.toNat (SubexpEnumerationPayload.scalarBits z) : ZMod p) = z
  rw [SubexpEnumerationPayload.scalarBits_value, ZMod.natCast_zmod_val]

def selectedInputCoefficients : Quad (Word (baseWidth p 1)) :=
  Quad.ofFn (fun i => selectedInputWord p (QuarticSearch.coefficients p i))

theorem selectedInputCoefficients_value :
    (selectedInputCoefficients p).map (SubexpWordLift.sourceValue p) =
      Quad.ofFn (QuarticSearch.coefficients p) := by
  simp [selectedInputCoefficients, Quad.map, Quad.ofFn]

/-- The selected-polynomial producer's forward byte output is exactly the
four-word input accepted by this setup, including coefficient order. -/
theorem selectedInputCoefficients_flat : flat (selectedInputCoefficients p) =
    SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode p)
      (QuarticSearch.coefficients p) := by
  simp [flat, SubexpQuarticFlatNeg.flat, SubexpQuarticFlatNeg.wordLists,
    FourWordPrograms.flatWords, Quad.toFn,
    selectedInputCoefficients, Quad.ofFn, selectedInputWord,
    SubexpTupleRefinement.encodeTuple, StackEncoding.encodeDataStack,
    List.ofFn_succ, SubexpEnumerationPayload.scalarCode]

def prepareMinusOne : Command :=
  stage SubexpNegationSetup.setupProgram (by decide) (by decide) [(4, 0), (3, 5)] [(8, 8)]
def liftCoefficients : Command :=
  stage SubexpFlatLift.program (by decide) (by decide) [(0, 5), (2, 8), (0, 10), (4, 11)] [(8, 5)]
def negateCoefficients : Command :=
  stage SubexpQuarticFlatNeg.program (by decide) (by decide) [(8, 4), (3, 14), (5, 18), (4, 20)] [(19, 5)]

omit [Fact (Nat.Prime p)] in
theorem prepareMinusOne_step (a : Data) (W : ℕ) (ha : StackBound a W)
    (hm : cacheWords a 3 = modulusWord p μ) (hw : cacheWords a 4 = widthWord p μ) :
    Step prepareMinusOne a W (39 * baseWidth p μ + 55 + 200 * (W + 1)) 8 (minusOne p μ).val := by
  obtain ⟨rf, ht⟩ := SubexpNegationSetup.setup_execute (fun _ => false)
    (widthWord p μ) (modulusWord p μ)
  have hn : 25 * (modulusWord p μ).length + 14 * (widthWord p μ).length + 30 =
      39 * baseWidth p μ + 55 := by simp; omega
  rw [hn] at ht
  let start : StructuredProgram.State 8 9 :=
    ⟨fun _ => false, SubexpNegationProgram.state (widthWord p μ) (modulusWord p μ) []⟩
  let out : StructuredProgram.State 8 9 :=
    ⟨rf, SubexpNegationProgram.state (widthWord p μ) (modulusWord p μ) (minusOne p μ).val⟩
  have hl : SubexpSetupStorage.project (registers (by decide : 8 ≤ 9))
      (work (by decide : 9 ≤ 24)) (prepared (by decide : 9 ≤ 24) [(4, 0), (3, 5)] a) = start := by
    apply prepared_eq _ _ _ _ _ (by decide) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hw.symm
      · exact hm.symm
    · intro j hj
      have h0 := hj (4, 0) (by simp)
      have h5 := hj (3, 5) (by simp)
      fin_cases j <;> simp_all [start, SubexpNegationProgram.state,
        SubexpNegationProgram.extendEight, ModularRingPrograms.extendSeven,
        ModularDivisionPrograms.resting, ModularDivisionPrograms.seven]
  have hmw : baseWidth p μ + 1 ≤ W := by
    have h := ha (cache 3)
    change (cacheWords a 3).length ≤ W at h
    simpa only [hm, modulusWord_length] using h
  have hbw : baseWidth p μ ≤ W := by
    have h := ha (cache 4)
    change (cacheWords a 4).length ≤ W at h
    simpa only [hw, widthWord_length] using h
  have ho : StackBound out W := by
    intro i
    fin_cases i <;> simp [out, SubexpNegationProgram.state,
      SubexpNegationProgram.extendEight, ModularRingPrograms.extendSeven,
      ModularDivisionPrograms.resting, ModularDivisionPrograms.seven,
      (minusOne p μ).property] <;> omega
  exact run_one SubexpNegationSetup.setupProgram (by decide) (by decide) [(4, 0), (3, 5)] 8 8 a
    start out ha (by decide) (by decide) ho hl ht

theorem liftCoefficients_step (hμ : 0 < μ) (a : Data) (W : ℕ)
    (coeff : Quad (Word (baseWidth p 1))) (ha : StackBound a W)
    (hp : cacheWords a 0 = primeWord p) (hc : cacheWords a 2 = flat coeff)
    (hw : cacheWords a 4 = widthWord p μ) (h4B : 4 * baseWidth p μ ≤ W) :
    Step liftCoefficients a W
      (2100 * (baseWidth p 1 + baseWidth p μ + 2)^2 + 200 * (W + 1)) 5 (flat (lifted p μ coeff)) := by
  have hb : (primeWord p).length = baseWidth p 1 := by simp [baseWidth]
  obtain ⟨rf, ht⟩ := SubexpFlatLift.program_runs p μ (sourceModulus p) hμ (fun _ => false)
    coeff (primeWord p) (widthWord p μ) (fun _ => []) hb (widthWord_length p μ)
  simp only [lift_encode_eq_flat] at ht
  let start := SubexpFlatLift.ready (fun _ => false) (primeWord p) (flat coeff) []
    (primeWord p) (widthWord p μ) (fun _ => [])
  let out := SubexpFlatLift.ready rf (primeWord p) (flat (lifted p μ coeff)) []
    (primeWord p) (widthWord p μ) (fun _ => [])
  have hl : SubexpSetupStorage.project (registers (by decide : 8 ≤ 9))
      (work (by decide : 20 ≤ 24))
      (prepared (by decide : 20 ≤ 24) [(0, 5), (2, 8), (0, 10), (4, 11)] a) = start := by
    apply prepared_eq _ _ _ _ _ (by decide) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hp.symm
      · exact hc.symm
      · exact hp.symm
      · exact hw.symm
    · intro j hj
      have h5 := hj (0, 5) (by simp)
      have h8 := hj (2, 8) (by simp)
      have h10 := hj (0, 10) (by simp)
      have h11 := hj (4, 11) (by simp)
      fin_cases j <;> simp_all [start, SubexpFlatLift.ready, SubexpFlatLift.state,
        SubexpFlatLift.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod]
  have hpw : Nat.log 2 p + 1 ≤ W := by
    have h := ha (cache 0)
    change (cacheWords a 0).length ≤ W at h
    simpa only [hp, primeWord_length] using h
  have hbw : baseWidth p μ ≤ W := by
    have h := ha (cache 4)
    change (cacheWords a 4).length ≤ W at h
    simpa only [hw, widthWord_length] using h
  have ho : StackBound out W := by
    intro i
    fin_cases i <;> simp [out, SubexpFlatLift.ready, SubexpFlatLift.state,
      SubexpFlatLift.stackArray, Fin.addCases, Fin.coe_ofNat_eq_mod, flat_length] <;> omega
  exact run_one SubexpFlatLift.program (by decide) (by decide) [(0, 5), (2, 8), (0, 10), (4, 11)]
    8 5 a start out ha (by decide) (by decide) ho hl ht

theorem negateCoefficients_step (a : Data) (W : ℕ)
    (coeff : Quad (Word (baseWidth p 1))) (ha : StackBound a W)
    (hm : cacheWords a 3 = modulusWord p μ) (hw : cacheWords a 4 = widthWord p μ)
    (hc : cacheWords a 5 = flat (lifted p μ coeff)) (hone : cacheWords a 8 = (minusOne p μ).val)
    (h4B : 4 * baseWidth p μ ≤ W) :
    Step negateCoefficients a W (25000 * (baseWidth p μ + 1)^2 + 200 * (W + 1))
      5 (flat (reduction p μ coeff)) := by
  obtain ⟨rf, ht⟩ := SubexpQuarticFlatNeg.program_run p μ (modulus p μ)
    (lifted p μ coeff) (minusOne p μ) (widthWord p μ) (widthWord_length p μ) (fun _ => false)
  let start : StructuredProgram.State 8 24 := ⟨fun _ => false,
    SubexpQuarticFlatNeg.initialStore (lifted p μ coeff) (minusOne p μ)
      (modulusWord p μ) (widthWord p μ)⟩
  let out : StructuredProgram.State 8 24 := ⟨rf,
    SubexpQuarticFlatNeg.finalStore (lifted p μ coeff) (reduction p μ coeff) (minusOne p μ)
      (modulusWord p μ) (widthWord p μ)⟩
  have hl : SubexpSetupStorage.project (registers (by decide : 8 ≤ 9))
      (work (by decide : 24 ≤ 24))
      (prepared (by decide : 24 ≤ 24) [(8, 4), (3, 14), (5, 18), (4, 20)] a) = start := by
    apply prepared_eq _ _ _ _ _ (by decide) (by intro j; rfl)
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hone.symm
      · exact hm.symm
      · exact hc.symm
      · exact hw.symm
    · intro j hj
      have h4 := hj (8, 4) (by simp)
      have h14 := hj (3, 14) (by simp)
      have h18 := hj (5, 18) (by simp)
      have h20 := hj (4, 20) (by simp)
      fin_cases j <;> simp_all [start, SubexpQuarticFlatNeg.initialStore,
        SubexpQuarticFlatNeg.bankStore, SubexpQuarticFlatNeg.emptyBank]
  have hmw : baseWidth p μ + 1 ≤ W := by
    have h := ha (cache 3)
    change (cacheWords a 3).length ≤ W at h
    simpa only [hm, modulusWord_length] using h
  have hbw : baseWidth p μ ≤ W := by
    have h := ha (cache 4)
    change (cacheWords a 4).length ≤ W at h
    simpa only [hw, widthWord_length] using h
  have ho : StackBound out W := by
    intro i
    fin_cases i <;> simp [out, SubexpQuarticFlatNeg.finalStore,
      SubexpQuarticFlatNeg.bankStore, SubexpQuarticFlatNeg.emptyBank,
      SubexpQuarticFlatNeg.flat_length, (minusOne p μ).property] <;> omega
  exact run_one SubexpQuarticFlatNeg.program (by decide) (by decide)
    [(8, 4), (3, 14), (5, 18), (4, 20)] 19 5 a start out ha (by decide) (by decide) ho hl ht

theorem lifted_value (hμ : 0 < μ) (a : Quad (Word (baseWidth p 1))) :
    (lifted p μ a).map (wordValue p μ) =
      (a.map (SubexpWordLift.sourceValue p)).map (fun z : ZMod p => (z.val : ZMod (p^μ))) :=
  SubexpWordLift.liftQuadRun_correct p μ (sourceModulus p) hμ a

theorem reduction_value (hμ : 0 < μ) (a : Quad (Word (baseWidth p 1)))
    (ha : a.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    (reduction p μ a).map (wordValue p μ) = reductionData (QuarticSearch.liftedCoefficients p μ) := by
  rw [reduction, SubexpQuarticNegMachine.negateWords_value _ _ _ _ _ (minusOne_value p μ),
    lifted_value p μ hμ a, ha]
  rfl

/-- The two negation implementations produce identical canonical words,
not merely the same quotient element. -/
theorem reduction_eq_prepareReduction (a : Quad (Word (baseWidth p 1))) :
    reduction p μ a =
      (SubexpPreparedQuartic.prepareReduction p μ (modulus p μ) (lifted p μ a)).1 := by
  apply SubexpCanonicalWords.quad_eq_of_values_eq p μ
  · exact ⟨SubexpCanonicalWords.wordMul_canonical p μ (modulus p μ) _ _,
      SubexpCanonicalWords.wordMul_canonical p μ (modulus p μ) _ _,
      SubexpCanonicalWords.wordMul_canonical p μ (modulus p μ) _ _,
      SubexpCanonicalWords.wordMul_canonical p μ (modulus p μ) _ _⟩
  · exact SubexpCanonicalWords.binaryNeg_canonical p μ (modulus p μ) _
  · rw [reduction, SubexpQuarticNegMachine.negateWords_value _ _ _ _ _ (minusOne_value p μ)]
    exact (SubexpPreparedQuartic.binaryNeg_correct p μ (modulus p μ) (lifted p μ a)).symm

def arithmeticCommand : Command :=
  .seq SubexpPreparedQuarticPrelude.command
    (.seq prepareMinusOne (.seq liftCoefficients negateCoefficients))

def finalWords (old : Cache → List Bool) (coeff : Quad (Word (baseWidth p 1))) :
    Cache → List Bool :=
  Function.update
    (Function.update (SubexpPreparedQuarticPrelude.resultWords old p μ)
      8 (minusOne p μ).val) 5 (flat (reduction p μ coeff))

def arithmeticBound (W : ℕ) (prime precision : List Bool) : ℕ :=
  SubexpPreparedQuarticPrelude.runtimeBound p μ W prime precision +
    (39 * baseWidth p μ + 55) +
    2100 * (baseWidth p 1 + baseWidth p μ + 2)^2 +
    25000 * (baseWidth p μ + 1)^2 + 600 * (W + 1)

theorem arithmeticCommand_run (hμ : 0 < μ) (a : Data) (W : ℕ)
    (coeff : Quad (Word (baseWidth p 1))) (ha : StackBound a W)
    (hp : BinaryArithmetic.toNat (cacheWords a 0) = p) (he : BinaryArithmetic.toNat (cacheWords a 1) = μ)
    (hc : cacheWords a 2 = flat coeff) (hb : Nat.log 2 p + 1 ≤ W)
    (hB : baseWidth p μ + 1 ≤ W) (h4B : 4 * baseWidth p μ ≤ W) :
    ∃ n b, Eval arithmeticCommand n a b ∧
      n ≤ arithmeticBound p μ W (cacheWords a 0) (cacheWords a 1) ∧
      StackBound b W ∧ cacheWords b = finalWords p μ (cacheWords a) coeff := by
  obtain ⟨n0, a0, e0, b0, w0, c0⟩ :=
    SubexpPreparedQuarticPrelude.command_run a W p μ ha (Fact.out : p.Prime).pos hμ hp he hb hB h4B
  have m0 : cacheWords a0 3 = modulusWord p μ := by
    rw [c0]; simp [SubexpPreparedQuarticPrelude.resultWords]
  have s0 : cacheWords a0 4 = widthWord p μ := by
    rw [c0]; simp [SubexpPreparedQuarticPrelude.resultWords]
  obtain ⟨n1, a1, e1, b1, w1, c1⟩ := prepareMinusOne_step p μ a0 W w0 m0 s0
  have p1 : cacheWords a1 0 = primeWord p := by
    rw [c1, c0]; simp [SubexpPreparedQuarticPrelude.resultWords]
  have c1' : cacheWords a1 2 = flat coeff := by
    rw [c1, c0]; simpa [SubexpPreparedQuarticPrelude.resultWords] using hc
  have s1 : cacheWords a1 4 = widthWord p μ := by rw [c1]; simpa using s0
  obtain ⟨n2, a2, e2, b2, w2, c2⟩ :=
    liftCoefficients_step p μ hμ a1 W coeff w1 p1 c1' s1 h4B
  have m2 : cacheWords a2 3 = modulusWord p μ := by rw [c2, c1]; simpa using m0
  have s2 : cacheWords a2 4 = widthWord p μ := by rw [c2, c1]; simpa using s0
  have c2' : cacheWords a2 5 = flat (lifted p μ coeff) := by rw [c2]; simp
  have o2 : cacheWords a2 8 = (minusOne p μ).val := by rw [c2, c1]; simp
  obtain ⟨n3, a3, e3, b3, w3, c3⟩ :=
    negateCoefficients_step p μ a2 W coeff w2 m2 s2 c2' o2 h4B
  refine ⟨n0 + (n1 + (n2 + n3)), a3, e0.seq (e1.seq (e2.seq e3)), ?_, w3, ?_⟩
  · unfold arithmeticBound
    omega
  · funext i
    by_cases hi : i = 5
    · subst i; simp [c3, finalWords]
    · simp [c3, c2, c1, c0, finalWords, hi]

def cleanupPorts : List (Fin 34) := ports (by decide : 24 ≤ 24) ++ [temporary]
def command : Command := .seq arithmeticCommand (SubexpSetupStorage.clearMany cleanupPorts)
def program := compiled command (cache 0) (cache 5)

def runtimeBound (W : ℕ) (prime precision : List Bool) : ℕ :=
  arithmeticBound p μ W prime precision + 25 * (2 * W + 3) + 1

theorem command_run (hμ : 0 < μ) (a : Data) (W : ℕ)
    (coeff : Quad (Word (baseWidth p 1))) (ha : StackBound a W)
    (hp : BinaryArithmetic.toNat (cacheWords a 0) = p) (he : BinaryArithmetic.toNat (cacheWords a 1) = μ)
    (hc : cacheWords a 2 = flat coeff) (hb : Nat.log 2 p + 1 ≤ W)
    (hB : baseWidth p μ + 1 ≤ W) (h4B : 4 * baseWidth p μ ≤ W) :
    ∃ b, RunsIn program (runtimeBound p μ W (cacheWords a 0) (cacheWords a 1))
      (a.withPC (some program.entry)) (b.withPC none) ∧
      StackBound b W ∧ cacheWords b = finalWords p μ (cacheWords a) coeff ∧
      (∀ j : Fin 24, b.stacks (work (by decide) j) = []) ∧ b.stacks temporary = [] := by
  obtain ⟨n, b, hn, hbnd, hw, hcaches⟩ :=
    arithmeticCommand_run p μ hμ a W coeff ha hp he hc hb hB h4B
  let out := SubexpSetupStorage.clearManyState cleanupPorts b
  have heval := hn.seq (SubexpSetupStorage.clearMany_eval cleanupPorts b)
  have hcost := clearManyCost_le cleanupPorts b hw
  have hlen : cleanupPorts.length = 25 := by simp [cleanupPorts, ports]
  rw [hlen] at hcost
  refine ⟨out, ⟨_, ?_, compiled_halt_trace heval (cache 0) (cache 5)⟩,
    clearMany_bound cleanupPorts b hw, ?_, ?_, ?_⟩
  · unfold runtimeBound
    omega
  · funext i
    change out.stacks (cache i) = _
    have hi : cache i ∉ cleanupPorts := by
      simp [cleanupPorts, cache_not_ports, cache_ne_temporary]
    rw [show out.stacks (cache i) = b.stacks (cache i) by
      change (SubexpSetupStorage.clearManyState cleanupPorts b).stacks (cache i) = _
      rw [SubexpSetupStorage.clearMany_stacks, ite_eq_right hi]]
    exact congrFun hcaches i
  · intro j
    change (SubexpSetupStorage.clearManyState cleanupPorts b).stacks _ = []
    rw [SubexpSetupStorage.clearMany_stacks, ite_eq_left]
    exact List.mem_append_left _ (work_mem_ports (by decide) j)
  · change (SubexpSetupStorage.clearManyState cleanupPorts b).stacks temporary = []
    rw [SubexpSetupStorage.clearMany_stacks, ite_eq_left]
    simp [cleanupPorts]

theorem program_primitive (hμ : 0 < μ) (a : Data) (W : ℕ)
    (coeff : Quad (Word (baseWidth p 1))) (ha : StackBound a W)
    (hp : BinaryArithmetic.toNat (cacheWords a 0) = p) (he : BinaryArithmetic.toNat (cacheWords a 1) = μ)
    (hc : cacheWords a 2 = flat coeff) (hb : Nat.log 2 p + 1 ≤ W)
    (hB : baseWidth p μ + 1 ≤ W) (h4B : 4 * baseWidth p μ ≤ W) :
    ∃ b, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * runtimeBound p μ W (cacheWords a 0) (cacheWords a 1))
      (primitiveCfg program (a.withPC (some program.entry)))
      (primitiveCfg program (b.withPC none)) ∧
      cacheWords b = finalWords p μ (cacheWords a) coeff := by
  obtain ⟨b, ht, _, hcache, _, _⟩ := command_run p μ hμ a W coeff ha hp he hc hb hB h4B
  exact ⟨b, primitive_execution program ht, hcache⟩

def initialState (prime precision : List Bool) (coeff : Quad (Word (baseWidth p 1))) : Data :=
  ⟨fun _ => false,
    Function.update
      (Function.update (Function.update (fun _ => []) (cache 0) prime) (cache 1) precision)
      (cache 2) (flat coeff)⟩

def storageBound (prime precision : List Bool) : ℕ :=
  prime.length + precision.length + 4 * baseWidth p 1 + 4 * baseWidth p μ + 4

omit [Fact (Nat.Prime p)] in
theorem initial_cache (prime precision : List Bool) (coeff : Quad (Word (baseWidth p 1))) :
    cacheWords (initialState p prime precision coeff) =
      ![prime, precision, flat coeff, [], [], [], [], [], []] := by
  funext i
  fin_cases i <;> simp [cacheWords, initialState, cache,
    Fin.ext_iff, Fin.coe_ofNat_eq_mod]

omit [Fact (Nat.Prime p)] in
theorem initial_bound (prime precision : List Bool) (coeff : Quad (Word (baseWidth p 1))) :
    StackBound (initialState p prime precision coeff) (storageBound p μ prime precision) := by
  intro i
  fin_cases i <;>
    simp [initialState, cache, flat_length, storageBound] <;> omega

/-- A complete measured run from runtime input words and a physically supplied
coefficient quartet. The trace starts with empty scratch, and ends with every
work stack and the copy temporary empty. -/
theorem run (hμ : 0 < μ) (prime precision : List Bool)
    (coeff : Quad (Word (baseWidth p 1)))
    (hp : BinaryArithmetic.toNat prime = p) (he : BinaryArithmetic.toNat precision = μ) :
    ∃ b, RunsIn program (runtimeBound p μ (storageBound p μ prime precision) prime precision)
      ((initialState p prime precision coeff).withPC (some program.entry)) (b.withPC none) ∧
      cacheWords b = ![primeWord p, precision, flat coeff, modulusWord p μ, widthWord p μ,
        flat (reduction p μ coeff), literalQuartet (baseWidth p μ) false,
        literalQuartet (baseWidth p μ) true, (minusOne p μ).val] ∧
      (∀ j : Fin 24, b.stacks (work (by decide) j) = []) ∧ b.stacks temporary = [] := by
  have hb : Nat.log 2 p + 1 ≤ storageBound p μ prime precision := by
    unfold storageBound baseWidth
    omega
  have hB : baseWidth p μ + 1 ≤ storageBound p μ prime precision := by
    unfold storageBound
    omega
  have h4B : 4 * baseWidth p μ ≤ storageBound p μ prime precision := by
    unfold storageBound
    omega
  have hprime : BinaryArithmetic.toNat
      (cacheWords (initialState p prime precision coeff) 0) = p := by
    rw [initial_cache]
    change BinaryArithmetic.toNat prime = p
    exact hp
  have hprecision : cacheWords (initialState p prime precision coeff) 1 = precision := by
    rw [initial_cache]
    rfl
  obtain ⟨b, ht, _, hc, hs, htmp⟩ := command_run p μ hμ
    (initialState p prime precision coeff) (storageBound p μ prime precision) coeff
    (initial_bound p μ prime precision coeff)
    hprime
    (by rw [hprecision]; exact he)
    (by rw [initial_cache]; rfl) hb hB h4B
  refine ⟨b, ?_, ?_, hs, htmp⟩
  · rw [hprecision] at ht
    exact ht
  · rw [hc, initial_cache]
    funext i
    fin_cases i <;> simp [finalWords, SubexpPreparedQuarticPrelude.resultWords]

theorem fixedBits_zero (B : ℕ) : fixedBits B 0 = List.replicate B false := by
  induction B with
  | zero => rfl
  | succ B ih => simp [fixedBits, ih, List.replicate_succ]

omit [Fact (Nat.Prime p)] in
theorem literalWord_eq_source (hμ : 0 < μ) (one : Bool) :
    literalWord (baseWidth p μ) one =
      (SubexpPreparedQuartic.literalWordRun p μ (SubexpConstantPrograms.literal one)).1.val := by
  have hpos : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.zero_lt_succ _)
  have hval : BinaryArithmetic.toNat (SubexpConstantPrograms.literal one) = bitVal one := by cases one <;> rfl
  have hfit : bitVal one < 2 ^ baseWidth p μ := by
    cases one
    · exact Nat.two_pow_pos _
    · exact Nat.one_lt_pow (Nat.ne_of_gt hpos) Nat.one_lt_two
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [literalWord_length]
    exact (SubexpModulusConstruction.normalizeRun_length _ _).symm
  · change BinaryArithmetic.toNat (fixedBits _ _) = BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ _).1
    rw [toNat_fixedBits_of_lt _ _ hfit,
      SubexpModulusConstruction.normalizeRun_value _ _ (by simpa only [hval] using hfit), hval]

omit [Fact (Nat.Prime p)] in
theorem literalZero_eq_source (hμ : 0 < μ) :
    literalQuartet (baseWidth p μ) false = flat (SubexpPreparedQuartic.prepareZero p μ).1 := by
  have hz := literalWord_eq_source p μ hμ false
  change literalWord (baseWidth p μ) false =
    (SubexpPreparedQuartic.literalWordRun p μ []).1.val at hz
  have hrep : (SubexpPreparedQuartic.literalWordRun p μ []).1.val =
      List.replicate (baseWidth p μ) false := by
    rw [← hz]
    exact fixedBits_zero _
  change literalWord (baseWidth p μ) false ++ List.replicate (3 * baseWidth p μ) false =
    (SubexpPreparedQuartic.literalWordRun p μ []).1.val ++
      ((SubexpPreparedQuartic.literalWordRun p μ []).1.val ++
        ((SubexpPreparedQuartic.literalWordRun p μ []).1.val ++
          (SubexpPreparedQuartic.literalWordRun p μ []).1.val))
  rw [hrep]
  rw [show literalWord (baseWidth p μ) false =
    List.replicate (baseWidth p μ) false from fixedBits_zero _]
  simp only [← List.replicate_add]
  congr 1
  omega

omit [Fact (Nat.Prime p)] in
theorem literalOne_eq_source (hμ : 0 < μ) :
    literalQuartet (baseWidth p μ) true = flat (SubexpPreparedQuartic.prepareOne p μ).1 := by
  have hz := literalWord_eq_source p μ hμ false
  have ho := literalWord_eq_source p μ hμ true
  change literalWord (baseWidth p μ) false =
    (SubexpPreparedQuartic.literalWordRun p μ []).1.val at hz
  change literalWord (baseWidth p μ) true =
    (SubexpPreparedQuartic.literalWordRun p μ [true]).1.val at ho
  have hrep : (SubexpPreparedQuartic.literalWordRun p μ []).1.val =
      List.replicate (baseWidth p μ) false := by
    rw [← hz]
    exact fixedBits_zero _
  change literalWord (baseWidth p μ) true ++ List.replicate (3 * baseWidth p μ) false =
    (SubexpPreparedQuartic.literalWordRun p μ [true]).1.val ++
      ((SubexpPreparedQuartic.literalWordRun p μ []).1.val ++
        ((SubexpPreparedQuartic.literalWordRun p μ []).1.val ++
          (SubexpPreparedQuartic.literalWordRun p μ []).1.val))
  rw [← ho, hrep]
  simp only [← List.replicate_add]
  congr 2
  omega

omit [Fact (Nat.Prime p)] in
theorem modulus_eq_source : modulus p μ =
    (SubexpPreparedQuartic.prepareModulus p μ (primeWord p) (primeWord_value p) (primeWord_length p)).1 := by
  have hbits := SubexpPreparedQuartic.prepareModulus_bits p μ (primeWord p)
    (primeWord_value p) (primeWord_length p)
  cases he : (SubexpPreparedQuartic.prepareModulus p μ (primeWord p)
      (primeWord_value p) (primeWord_length p)).1 with
  | mk bits hlen hval =>
    rw [he] at hbits
    change bits = modulusWord p μ at hbits
    subst bits
    rfl

def initializedData (D : ℕ) (coeff : Quad (Word (baseWidth p 1))) :
    SubexpSymbolicCost.QuarticInitialization p D :=
  ⟨modulus p (D + 1), reduction p (D + 1) coeff,
    (SubexpPreparedQuartic.prepareZero p (D + 1)).1,
    (SubexpPreparedQuartic.prepareOne p (D + 1)).1⟩

/-- Exact source-initializer bridge for all four retained caches. The incoming
coefficient words are first lifted by the actual four-word lift routine. -/
theorem initializedData_eq_source (D : ℕ) (coeff : Quad (Word (baseWidth p 1))) :
    initializedData p D coeff =
      (SubexpSymbolicCost.initializeQuartic p D (primeWord p)
        (primeWord_value p) (primeWord_length p) (lifted p (D + 1) coeff)).1 := by
  simp only [initializedData, SubexpSymbolicCost.initializeQuartic]
  rw [← modulus_eq_source, ← reduction_eq_prepareReduction]

def preparedData (D : ℕ) (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    SubexpSelectedConversions.Prepared p D where
  modulus := modulus p (D + 1)
  reduction := reduction p (D + 1) coeff
  zero := (SubexpPreparedQuartic.prepareZero p (D + 1)).1
  one := (SubexpPreparedQuartic.prepareOne p (D + 1)).1
  reduction_spec := reduction_value p (D + 1) (Nat.zero_lt_succ _) coeff hc
  zero_spec := SubexpPreparedQuartic.prepareZero_quotient p (D + 1) _
  one_spec := SubexpPreparedQuartic.prepareOne_quotient p (D + 1) (Nat.zero_lt_succ _) _

/-- The finite program physically installs the caches of a represented ring.
The only coefficient premise describes the earlier search stage's input
bytes; every prepared-cache equality is a conclusion of execution. -/
theorem run_prepared (D : ℕ) (prime precision : List Bool)
    (coeff : Quad (Word (baseWidth p 1)))
    (hp : BinaryArithmetic.toNat prime = p) (he : BinaryArithmetic.toNat precision = D + 1)
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    ∃ b, RunsIn program
      (runtimeBound p (D + 1) (storageBound p (D + 1) prime precision) prime precision)
      ((initialState p prime precision coeff).withPC (some program.entry)) (b.withPC none) ∧
      cacheWords b = ![primeWord p, precision, flat coeff,
        (preparedData p D coeff hc).modulus.bits, widthWord p (D + 1),
        flat (preparedData p D coeff hc).reduction,
        flat (preparedData p D coeff hc).zero,
        flat (preparedData p D coeff hc).one, (minusOne p (D + 1)).val] ∧
      (∀ j : Fin 24, b.stacks (work (by decide) j) = []) ∧ b.stacks temporary = [] := by
  obtain ⟨b, ht, hb, hs, htmp⟩ := run p (D + 1) (Nat.zero_lt_succ _) prime precision coeff hp he
  refine ⟨b, ht, ?_, hs, htmp⟩
  rw [literalZero_eq_source p (D + 1) (Nat.zero_lt_succ _),
    literalOne_eq_source p (D + 1) (Nat.zero_lt_succ _)] at hb
  exact hb

theorem bound_of_cache (a : Data) (W : ℕ)
    (hc : ∀ i, (cacheWords a i).length ≤ W)
    (hs : ∀ j : Fin 24, a.stacks (work (by decide) j) = [])
    (ht : a.stacks temporary = []) : StackBound a W := by
  intro i
  by_cases hi : i.val < 24
  · let j : Fin 24 := ⟨i.val, hi⟩
    have he : work (by decide) j = i := Fin.ext rfl
    rw [← he, hs]
    exact Nat.zero_le _
  · by_cases hit : i = temporary
    · rw [hit, ht]
      exact Nat.zero_le _
    · have hiv : i.val < 33 := by
        have hi34 := i.isLt
        have hi33 : i.val ≠ 33 := by
          intro he
          apply hit
          exact Fin.ext he
        omega
      let j : Cache := ⟨i.val - 24, by omega⟩
      have he : cache j = i := by apply Fin.ext; simp only [cache, j]; omega
      rw [← he]
      exact hc j

/-- The same stable output contract also carries the bound needed by callers
to charge physical copies into their own persistent banks. -/
theorem run_prepared_bounded (D : ℕ) (prime precision : List Bool)
    (coeff : Quad (Word (baseWidth p 1)))
    (hp : BinaryArithmetic.toNat prime = p) (he : BinaryArithmetic.toNat precision = D + 1)
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p)) :
    ∃ b, RunsIn program
      (runtimeBound p (D + 1) (storageBound p (D + 1) prime precision) prime precision)
      ((initialState p prime precision coeff).withPC (some program.entry)) (b.withPC none) ∧
      StackBound b (storageBound p (D + 1) prime precision) ∧
      cacheWords b = ![primeWord p, precision, flat coeff,
        (preparedData p D coeff hc).modulus.bits, widthWord p (D + 1),
        flat (preparedData p D coeff hc).reduction,
        flat (preparedData p D coeff hc).zero,
        flat (preparedData p D coeff hc).one, (minusOne p (D + 1)).val] ∧
      (∀ j : Fin 24, b.stacks (work (by decide) j) = []) ∧ b.stacks temporary = [] := by
  obtain ⟨b, ht, hb, hs, htmp⟩ := run_prepared p D prime precision coeff hp he hc
  refine ⟨b, ht, ?_, hb, hs, htmp⟩
  apply bound_of_cache b _ _ hs htmp
  intro i
  rw [hb]
  fin_cases i <;> simp [preparedData, modulus, (minusOne p (D + 1)).property,
      storageBound]
  all_goals first
    | rw [flat_length]
    | simp [baseWidth]
      omega

end SubexponentialSAT.SubexpPreparedQuarticSetup

end OAI.Algorithms
