import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConcreteMomentPhase
import OAI.Algorithms.SubexponentialSAT.SubexpDenseOperandBounds
import OAI.Algorithms.SubexponentialSAT.SubexpDenseServiceBounds

namespace OAI.Algorithms

/-! Bounds for the actual extraction phase. Serialized source bytes occur
linearly; parsing, dense evaluation, coefficient scans, cell updates, loop
tests, and zero-array initialization are all charged. -/

namespace SubexponentialSAT.SubexpMomentCostBounds

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpDenseSerialization SubexpExecution
open SubexpExtractionJobs SubexpMomentProgram

def sourceBytes {R : Type*} (encode : R → List Bool) (e : Algorithm.Expr R) : ℕ :=
  (SubexpPostfixControl.serializeCode encode e.compile).length

private theorem serialize_append {R : Type*} (encode : R → List Bool)
    (xs ys : List (Algorithm.Instr R)) :
    SubexpPostfixControl.serializeCode encode (xs ++ ys) =
      SubexpPostfixControl.serializeCode encode xs ++
        SubexpPostfixControl.serializeCode encode ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,
      SubexpPostfixControl.serializeCode, ih, List.append_assoc]

@[simp] theorem sourceBytes_lit {R : Type*} (encode : R → List Bool) (x : R) :
    sourceBytes encode (.lit x) = 2 * ((encode x).length + 1) := by
  simp [sourceBytes, Algorithm.Expr.compile, SubexpPostfixControl.serializeCode,
    SubexpPostfixControl.serializeInstr, Encoding.length_frame]
  all_goals omega

@[simp] theorem sourceBytes_add {R : Type*} (encode : R → List Bool)
    (e f : Algorithm.Expr R) :
    sourceBytes encode (.add e f) = sourceBytes encode e + sourceBytes encode f + 2 := by
  simp [sourceBytes, Algorithm.Expr.compile, serialize_append,
    SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr, Nat.add_assoc]

@[simp] theorem sourceBytes_mul {R : Type*} (encode : R → List Bool)
    (e f : Algorithm.Expr R) :
    sourceBytes encode (.mul e f) = sourceBytes encode e + sourceBytes encode f + 2 := by
  simp [sourceBytes, Algorithm.Expr.compile, serialize_append,
    SubexpPostfixControl.serializeCode, SubexpPostfixControl.serializeInstr, Nat.add_assoc]

/-- Each instruction is paid for by its actual postfix bytes. The LOAD
hypothesis explicitly includes the entire raw literal serialization. -/
theorem operationCost_le_sourceBytes {R : Type*} (ops : Operations R R)
    (encode : R → List Bool) (addBound mulBound : R → R → ℕ)
    (loadBound : R → ℕ) (K : ℕ) (hK : 17 ≤ K)
    (hl : ∀ x, loadBound x ≤ K * ((encode x).length + 1))
    (ha : ∀ e f : Algorithm.Expr R,
      addBound (evalWithCost ops e).1 (evalWithCost ops f).1 ≤ K)
    (hm : ∀ e f : Algorithm.Expr R,
      mulBound (evalWithCost ops e).1 (evalWithCost ops f).1 ≤ K)
    (e : Algorithm.Expr R) :
    SubexpProjectedEvaluation.operationCost ops encode addBound mulBound loadBound e ≤
      K * sourceBytes encode e := by
  induction e with
  | lit x =>
      have hx := hl x
      have hp : 11 * (encode x).length + 17 ≤ K * ((encode x).length + 1) := by
        nlinarith [Nat.mul_le_mul_right (encode x).length (show 11 ≤ K by omega)]
      simp only [SubexpProjectedEvaluation.operationCost, sourceBytes_lit]
      nlinarith
  | add e f he hf =>
      have hb := ha e f
      simp only [SubexpProjectedEvaluation.operationCost, sourceBytes_add]
      nlinarith
  | mul e f he hf =>
      have hb := hm e f
      simp only [SubexpProjectedEvaluation.operationCost, sourceBytes_mul]
      nlinarith

private theorem size_pos (p D : ℕ) : 1 ≤ parameterSize D 4 (Nat.log 2 p + 1) := by
  unfold parameterSize
  omega

private theorem monomial_pos (D : ℕ) : 1 ≤ monomialCount D :=
  Nat.choose_pos (by omega : D ≤ 3 * D + 1)

private theorem dim_le (p D : ℕ) : D + 1 ≤ parameterSize D 4 (Nat.log 2 p + 1) := by
  unfold parameterSize
  omega

private theorem width_le (p D : ℕ) :
    baseWidth p (D + 1) ≤ (parameterSize D 4 (Nat.log 2 p + 1))^2 := by
  have hb : Nat.log 2 p + 1 ≤ parameterSize D 4 (Nat.log 2 p + 1) := by
    unfold parameterSize
    omega
  simpa only [baseWidth, pow_two] using Nat.mul_le_mul (dim_le p D) hb

private theorem slots_le (p D : ℕ) :
    slotCount D ≤ monomialCount D * (parameterSize D 4 (Nat.log 2 p + 1))^2 := by
  apply Nat.mul_le_mul_left
  simpa only [pow_two] using Nat.mul_le_mul (dim_le p D)
    ((Nat.le_succ D).trans (dim_le p D))

private theorem powers_le (p D a b c d : ℕ) (ha : a ≤ c) (hb : b ≤ d) :
    (parameterSize D 4 (Nat.log 2 p + 1))^a * (monomialCount D)^b ≤
      (parameterSize D 4 (Nat.log 2 p + 1))^c * (monomialCount D)^d :=
  Nat.mul_le_mul (Nat.pow_le_pow_right (size_pos p D) ha)
    (Nat.pow_le_pow_right (monomial_pos D) hb)

def evaluationFactor (p D : ℕ) : ℕ :=
  2000000000 * (parameterSize D 4 (Nat.log 2 p + 1))^12 * (monomialCount D)^4

private theorem evaluationFactor_pos (p D : ℕ) : 17 ≤ evaluationFactor p D := by
  have h := powers_le p D 0 0 12 4 (by decide) (by decide)
  simp only [pow_zero, one_mul] at h
  unfold evaluationFactor
  nlinarith

section Concrete

variable (p D : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p (D + 1)) (t z o : QuarticCode p D)
  (slots : List (RawIndex D))

local notation "ops" => preparedProgram p D M t z o
local notation "enc" => encodeFixedQuarticCoefficients p D
local notation "S" => parameterSize D 4 (Nat.log 2 p + 1)
local notation "MX" => monomialCount D
local notation "addCost" => SubexpDenseOperands.addBound p D M t z o slots
local notation "mulCost" => SubexpDenseMultiplication.bound p D M t z o slots
local notation "loadCost" => SubexpDenseOperands.loadBound p D M t z o slots

/-- The actual finite LOAD/ADD/MUL services, including their serialized
parsers and output framing, give a linear source-byte bound. -/
theorem concrete_operationCost_le
    (hs : ∀ a ∈ slots, Retained D a) (hN : slots.length ≤ slotCount D)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    SubexpProjectedEvaluation.operationCost (programOperations ops slots)
      enc addCost mulCost loadCost e ≤ evaluationFactor p D * sourceBytes enc e := by
  apply operationCost_le_sourceBytes _ _ _ _ _ _ (evaluationFactor_pos p D)
  · intro P
    apply (SubexpDenseOperands.loadBound_le_uniform p D M t z o slots P hs hN).trans
    apply Nat.mul_le_mul_right
    have h := powers_le p D 6 1 12 4 (by decide) (by decide)
    simp only [pow_one] at h
    unfold evaluationFactor
    calc
      _ = 1280000 * (S^6 * MX) := by ring
      _ ≤ 2000000000 * (S^12 * MX^4) := Nat.mul_le_mul (by decide) h
      _ = _ := by ring
  · intro e f
    have he := programEval_retained ops slots hs e
    have hf := programEval_retained ops slots hs f
    have hel : (programEval ops slots e).1.length ≤ slotCount D := by
      rw [programEval_length]; exact hN
    have hfl : (programEval ops slots f).1.length ≤ slotCount D := by
      rw [programEval_length]; exact hN
    have h := SubexpDenseOperands.addBound_le_uniform p D M t z o slots
      (programEval ops slots e).1 (programEval ops slots f).1 he hf hs hel hfl hN
    change addCost (programEval ops slots e).1 (programEval ops slots f).1 ≤ _
    unfold evaluationFactor
    nlinarith
  · intro e f
    have he := programEval_retained ops slots hs e
    have hf := programEval_retained ops slots hs f
    have hel : (programEval ops slots e).1.length ≤ slotCount D := by
      rw [programEval_length]; exact hN
    have hfl : (programEval ops slots f).1.length ≤ slotCount D := by
      rw [programEval_length]; exact hN
    have h := SubexpDenseMultiplication.bound_le_uniform p D M t z o slots
      (programEval ops slots e).1 (programEval ops slots f).1 he hf hs hel hfl hN
    change mulCost (programEval ops slots e).1 (programEval ops slots f).1 ≤ _
    unfold evaluationFactor
    nlinarith

theorem resultBytes_le (hs : ∀ a ∈ slots, Retained D a)
    (hN : slots.length ≤ slotCount D)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D))) :
    (enc (programEval ops slots e).1).length ≤ 31 * S^4 * MX := by
  have hB := width_le p D
  have hI := indexBits_degree D 4 (Nat.log 2 p + 1)
  have hS := size_pos p D
  have hS2 : 1 ≤ S^2 := by nlinarith
  have hR : SubexpDenseProjectionBounds.recordBits (baseWidth p (D + 1)) (indexBits D)
      ≤ 30 * S^2 := by
    unfold SubexpDenseProjectionBounds.recordBits
    omega
  have hn := hN.trans (slots_le p D)
  have hunit := powers_le p D 0 0 4 1 (by decide) (by decide)
  simp only [pow_zero, pow_one, one_mul] at hunit
  rw [SubexpDenseProjectionBounds.retained_serialized_length p D _
    (programEval_retained ops slots hs e), programEval_length]
  calc
    _ ≤ 1 + (30 * S^2) * (MX * S^2) := by gcongr
    _ = 1 + 30 * (S^4 * MX) := by ring
    _ ≤ _ := by nlinarith

private def ancillaryCost (B I J O : ℕ) : ℕ :=
  38 * J + 44 * I + 9 * O + 14 * B +
    (9 * I + 4 * SubexpFlatAdd.wordCost B + 48 * B + 75) * (O + 1) +
    SubexpJetCellProgram.eventBudget B J + 140

omit [Fact p.Prime] in
private theorem ancillaryCost_le (I J O : ℕ)
    (hI : I ≤ indexBits D) (hJ : J ≤ D) (hO : O ≤ 31 * S^4 * MX) :
    ancillaryCost (baseWidth p (D + 1)) I J O ≤ 4000000 * S^12 * MX^4 := by
  let U := S^8 * MX
  have hS := size_pos p D
  have hD := dim_le p D
  have hB := width_le p D
  have hI2 : I ≤ 2 * S^2 := hI.trans (indexBits_degree D 4 (Nat.log 2 p + 1))
  have hS2 : 1 ≤ S^2 := by nlinarith
  have hS4 : 1 ≤ S^4 := by nlinarith
  have h24 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have hBp : baseWidth p (D + 1) + 1 ≤ 2 * S^2 := by omega
  have hBp2 : (baseWidth p (D + 1) + 1)^2 ≤ 4 * S^4 := by
    calc
      _ ≤ (2 * S^2)^2 := Nat.pow_le_pow_left hBp 2
      _ = _ := by ring
  have hscan : 9 * I + 4 * SubexpFlatAdd.wordCost (baseWidth p (D + 1)) +
      48 * baseWidth p (D + 1) + 75 ≤ 100000 * S^4 := by
    unfold SubexpFlatAdd.wordCost
    nlinarith
  have hunit4 := powers_le p D 0 0 4 1 (by decide) (by decide)
  simp only [pow_zero, pow_one, one_mul] at hunit4
  have hOp : O + 1 ≤ 32 * S^4 * MX := by nlinarith
  have hlookup :
      (9 * I + 4 * SubexpFlatAdd.wordCost (baseWidth p (D + 1)) +
        48 * baseWidth p (D + 1) + 75) * (O + 1) ≤ 3200000 * U := by
    calc
      _ ≤ (100000 * S^4) * (32 * S^4 * MX) := Nat.mul_le_mul hscan hOp
      _ = _ := by dsimp [U]; ring
  have hJp : J + 1 ≤ S := by omega
  have hevent : SubexpJetCellProgram.eventBudget (baseWidth p (D + 1)) J ≤
      120000 * S^5 := by
    calc
      _ ≤ 30000 * (J + 1) * (baseWidth p (D + 1) + 1)^2 := by
        have h := SubexpJetCellProgram.eventBudget_polynomial (baseWidth p (D + 1)) J
        omega
      _ ≤ 30000 * S * (4 * S^4) := by gcongr
      _ = _ := by ring
  have h1U : 1 ≤ U := by
    simpa only [U, pow_zero, pow_one, one_mul] using
      powers_le p D 0 0 8 1 (by decide) (by decide)
  have hSU : S ≤ U := by
    simpa only [U, pow_zero, pow_one, mul_one] using
      powers_le p D 1 0 8 1 (by decide) (by decide)
  have h2U : S^2 ≤ U := by
    simpa only [U, pow_zero, pow_one, mul_one] using
      powers_le p D 2 0 8 1 (by decide) (by decide)
  have h4U : S^4 * MX ≤ U := by
    simpa only [U, pow_one] using powers_le p D 4 1 8 1 (by decide) (by decide)
  have h5U : S^5 ≤ U := by
    simpa only [U, pow_zero, pow_one, mul_one] using
      powers_le p D 5 0 8 1 (by decide) (by decide)
  have hJU : J ≤ U := by omega
  have hIU : I ≤ 2 * U := by omega
  have hBU : baseWidth p (D + 1) ≤ U := hB.trans h2U
  have hOU : O ≤ 31 * U := by nlinarith
  have heventU : SubexpJetCellProgram.eventBudget (baseWidth p (D + 1)) J ≤
      120000 * U := hevent.trans (Nat.mul_le_mul_left _ h5U)
  have hsmall : ancillaryCost (baseWidth p (D + 1)) I J O ≤ 3500000 * U := by
    unfold ancillaryCost
    omega
  have hUH : U ≤ S^12 * MX^4 := by
    simpa only [U, pow_one] using powers_le p D 8 1 12 4 (by decide) (by decide)
  calc
    _ ≤ 3500000 * U := hsmall
    _ ≤ 4000000 * (S^12 * MX^4) := Nat.mul_le_mul (by decide) hUH
    _ = _ := by ring

/-- The entire ready-state job, including the outer record parser and loop
test. Raw source literals require no retained-key invariant. -/
theorem fullJobCost_le (hs : ∀ a ∈ slots, Retained D a)
    (hN : slots.length ≤ slotCount D) (j : Job)
    (e : Algorithm.Expr (CoeffList D (QuarticCode p D)))
    (hcode : j.sourceCode = SubexpPostfixControl.serializeCode enc e.compile)
    (hindex : j.outputIndex.length ≤ D) (hkey : j.coefficientKey.length ≤ indexBits D) :
    6 * j.encode.length +
      SubexpMomentStep.readyCost p D M t z o slots addCost mulCost loadCost j e + 7 ≤
        2 * evaluationFactor p D * (sourceBytes enc e + 1) := by
  let O := (enc (programEval ops slots e).1).length
  have hO : O ≤ 31 * S^4 * MX := resultBytes_le p D M t z o slots hs hN e
  have hlookup := SubexpCoefficientLookup.scan_budget_le_input (baseWidth p (D + 1))
    j.coefficientKey (SubexpCoefficientLookup.encoded p (D + 1)
      (SubexpMomentStep.encodedRecords (programEval ops slots e).1))
  rw [SubexpMomentStep.encodedRecords_bytes] at hlookup
  have hlen : j.encode.length =
      2 * (j.outputIndex.length + j.coefficientKey.length + sourceBytes enc e) + 3 := by
    simp only [Job.encode, List.length_append, Encoding.length_frame, hcode]
    unfold sourceBytes
    omega
  have hcodelen : j.sourceCode.length = sourceBytes enc e := by rw [hcode]; rfl
  have hraw : 6 * j.encode.length +
      SubexpMomentStep.readyCost p D M t z o slots addCost mulCost loadCost j e + 7 ≤
      SubexpProjectedEvaluation.operationCost (programOperations ops slots)
        enc addCost mulCost loadCost e + 45 * sourceBytes enc e +
        ancillaryCost (baseWidth p (D + 1)) j.coefficientKey.length j.outputIndex.length O := by
    unfold SubexpMomentStep.readyCost SubexpPreparedEvaluation.preparationCost
      SubexpAccumulateCoefficient.budget ancillaryCost
    rw [hlen, hcodelen]
    dsimp only [O] at *
    omega
  have hop := concrete_operationCost_le p D M t z o slots hs hN e
  have hanc := ancillaryCost_le p D j.coefficientKey.length j.outputIndex.length O hkey hindex hO
  have hancK : ancillaryCost (baseWidth p (D + 1)) j.coefficientKey.length
      j.outputIndex.length O ≤ evaluationFactor p D := by
    unfold evaluationFactor
    nlinarith
  have hunit := powers_le p D 0 0 12 4 (by decide) (by decide)
  simp only [pow_zero, one_mul] at hunit
  have h45 : 45 ≤ evaluationFactor p D := by unfold evaluationFactor; nlinarith
  have h45L := Nat.mul_le_mul_right (sourceBytes enc e) h45
  nlinarith

theorem generatedQuery_retained (q : Query D)
    (hq : q ∈ SubexpQueryOrder.generatedQueries D) :
    Retained D (q.exponent, (q.u, q.z)) := by
  have h := (mem_queries D q).mp ((SubexpQueryOrder.generatedQueries_perm D).mem_iff.mp hq)
  exact ⟨(Algorithm.mem_exponentList D (2 * D + 1) q.exponent).mp h.2.1, h.2.2, h.1⟩

/-- Complete concrete phase cost, including initialization. The source
generator's own cost is separate from these actual evaluation traces. -/
theorem generated_cost_le
    (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D)))
    (hs : ∀ a ∈ slots, Retained D a) (hN : slots.length ≤ slotCount D) (L : ℕ)
    (hsource : ∀ q ∈ SubexpQueryOrder.generatedQueries D,
      sourceBytes enc (source q.exponent) ≤ L) :
    SubexpConcreteMomentPhase.cost p D M t z o slots source
        (SubexpQueryOrder.generatedQueries D) ≤
      5000000000 * S^14 * MX^5 * (L + 1) := by
  have hphase := SubexpMomentPhase.generated_phaseCost_le p D M t z o slots source
    addCost mulCost loadCost (2 * evaluationFactor p D * (L + 1)) (by
      intro q hq
      have hret := generatedQuery_retained D q hq
      have hindex : (SubexpMomentPhase.job p D source q).outputIndex.length ≤ D := by
        simpa only [SubexpMomentPhase.job, List.length_replicate] using Nat.le_of_lt hret.2.2
      have hkey : (SubexpMomentPhase.job p D source q).coefficientKey.length ≤ indexBits D :=
        (fixedKey_length _ hret).le
      have h := fullJobCost_le p D M t z o slots hs hN
        (SubexpMomentPhase.job p D source q) (source q.exponent) rfl hindex hkey
      exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (hsource q hq) 1)))
  have hS := size_pos p D
  have hD := dim_le p D
  have hB := width_le p D
  have hD' : D ≤ S := by omega
  have h13 : S ≤ S^3 := by simpa using Nat.pow_le_pow_right hS (show 1 ≤ 3 by decide)
  have h23 : S^2 ≤ S^3 := Nat.pow_le_pow_right hS (by decide)
  have h03 : 1 ≤ S^3 := by simpa using Nat.pow_le_pow_right hS (show 0 ≤ 3 by decide)
  have hDB : D * baseWidth p (D + 1) ≤ S^3 := by
    calc
      _ ≤ S * S^2 := Nat.mul_le_mul hD' hB
      _ = _ := by ring
  have hinit : 14 * baseWidth p (D + 1) + D * (28 * baseWidth p (D + 1) + 14) + 20 ≤
      76 * S^3 := by nlinarith
  have hcount : D * ((3 * D + 1).choose D) * (D + 1) ≤ S^2 * MX := by
    calc
      _ = (D * (D + 1)) * MX := by unfold monomialCount; ring
      _ ≤ (S * S) * MX := Nat.mul_le_mul_right _ (Nat.mul_le_mul hD' hD)
      _ = _ := by ring
  have hwork : 2 * evaluationFactor p D * (L + 1) *
      (D * ((3 * D + 1).choose D) * (D + 1)) ≤
      4000000000 * S^14 * MX^5 * (L + 1) := by
    calc
      _ ≤ 2 * evaluationFactor p D * (L + 1) * (S^2 * MX) := Nat.mul_le_mul_left _ hcount
      _ = _ := by unfold evaluationFactor; ring
  have hsmall := powers_le p D 3 0 14 5 (by decide) (by decide)
  simp only [pow_zero, mul_one] at hsmall
  have hsmallL : S^3 ≤ S^14 * MX^5 * (L + 1) :=
    hsmall.trans (by nlinarith)
  change SubexpMomentPhase.phaseCost p D M t z o slots source
    addCost mulCost loadCost _ ≤ _
  nlinarith

end Concrete

end SubexponentialSAT.SubexpMomentCostBounds

end OAI.Algorithms
