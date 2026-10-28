import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-!
# Quartic operations with a stored modulus

The modulus is input data. None of the operations in this file computes
`p^mu`, its bit expansion, or an irreducible polynomial. Setup is separate.
-/

namespace SubexponentialSAT.SubexpPreparedQuartic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Prepared bytes together with their mathematical interpretation. -/
structure Modulus (p μ : ℕ) where
  bits : List Bool
  length_le : bits.length ≤ baseWidth p μ + 1
  value : BinaryArithmetic.toNat bits = p^μ

variable (p μ : ℕ) [Fact p.Prime]

/-- A specification-level constructor. The counted setup implementation can
instead pass its computed bytes directly to the `Modulus` constructor. -/
def canonicalModulus : Modulus p μ :=
  ⟨modulusBits p μ, (modulusBits_length p μ).le, modulusBits_value p μ⟩

/-- Actual setup computes the modulus from the supplied prime word using
binary multiplication. Natural exponentiation appears only in the proof. -/
def prepareModulus (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p) (hwidth : primeBits.length = Nat.log 2 p + 1) :
    Modulus p μ × ℕ :=
  let out := SubexpModulusConstruction.powerRun primeBits μ
  (⟨out.1, (SubexpModulusConstruction.modulus_length p μ primeBits hwidth).le,
    SubexpModulusConstruction.modulus_value p μ primeBits hvalue⟩, out.2.length)

omit [Fact (Nat.Prime p)] in
theorem prepareModulus_bits (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p) (hwidth : primeBits.length = Nat.log 2 p + 1) :
    (prepareModulus p μ primeBits hvalue hwidth).1.bits = modulusBits p μ :=
  SubexpModulusConstruction.modulus_eq_fixedBits p μ primeBits hvalue hwidth

omit [Fact (Nat.Prime p)] in
theorem prepareModulus_cost (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p) (hwidth : primeBits.length = Nat.log 2 p + 1) :
    (prepareModulus p μ primeBits hvalue hwidth).2 ≤
      (2 + μ * (1 + 40 * (primeBits.length + 1) *
        (primeBits.length + 2 + 2 * μ * primeBits.length))) +
          (3 * (1 + μ * primeBits.length) + 1) :=
  SubexpModulusConstruction.powerRun_cost primeBits μ

omit [Fact (Nat.Prime p)] in
theorem prepareModulus_cost_quadratic (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p) (hwidth : primeBits.length = Nat.log 2 p + 1) :
    (prepareModulus p μ primeBits hvalue hwidth).2 ≤
      100 * (μ + 1)^2 * (primeBits.length + 1)^2 :=
  SubexpModulusConstruction.powerRun_cost_quadratic primeBits μ

/-- The same explicit traced copying/padding routine prepares literal words.
Its input is a fixed literal list, never a natural-number residue conversion. -/
def literalWordRun (literal : List Bool) : Word (baseWidth p μ) × ℕ :=
  let out := SubexpModulusConstruction.normalizeRun (baseWidth p μ) literal
  (⟨out.1, SubexpModulusConstruction.normalizeRun_length _ _⟩, out.2.length)

omit [Fact (Nat.Prime p)] in
theorem literalWordRun_cost (literal : List Bool) :
    (literalWordRun p μ literal).2 = 3 * baseWidth p μ + 1 :=
  SubexpModulusConstruction.normalizeRun_cost _ _

omit [Fact (Nat.Prime p)] in
@[simp] theorem literalWordRun_zero :
    wordValue p μ (literalWordRun p μ []).1 = 0 := by
  change (BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ []).1 : ZMod (p^μ)) = 0
  rw [SubexpModulusConstruction.normalizeRun_value]
  · simp [SubexponentialSAT.BinaryArithmetic.toNat]
  · exact Nat.two_pow_pos _

omit [Fact (Nat.Prime p)] in
theorem literalWordRun_one (hμ : 0 < μ) :
    wordValue p μ (literalWordRun p μ [true]).1 = 1 := by
  have hB : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.zero_lt_succ _)
  have hone : BinaryArithmetic.toNat [true] < 2^baseWidth p μ :=
    Nat.one_lt_pow (Nat.ne_of_gt hB) Nat.one_lt_two
  change (BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ [true]).1 : ZMod (p^μ)) = 1
  rw [SubexpModulusConstruction.normalizeRun_value _ _ hone]
  simp [SubexponentialSAT.BinaryArithmetic.toNat,
    SubexponentialSAT.BinaryArithmetic.bitVal]

/-- Four literal-word constructions, including all copying/padding events. -/
def prepareZero : Quad (Word (baseWidth p μ)) × ℕ :=
  let a := literalWordRun p μ []
  let b := literalWordRun p μ []
  let c := literalWordRun p μ []
  let d := literalWordRun p μ []
  (⟨a.1, b.1, c.1, d.1⟩, a.2 + b.2 + c.2 + d.2)

def prepareOne : Quad (Word (baseWidth p μ)) × ℕ :=
  let a := literalWordRun p μ [true]
  let b := literalWordRun p μ []
  let c := literalWordRun p μ []
  let d := literalWordRun p μ []
  (⟨a.1, b.1, c.1, d.1⟩, a.2 + b.2 + c.2 + d.2)

omit [Fact (Nat.Prime p)] in
theorem prepareZero_cost : (prepareZero p μ).2 = 12 * baseWidth p μ + 4 := by
  simp [prepareZero, literalWordRun_cost]
  omega

omit [Fact (Nat.Prime p)] in
theorem prepareOne_cost : (prepareOne p μ).2 = 12 * baseWidth p μ + 4 := by
  simp [prepareOne, literalWordRun_cost]
  omega

omit [Fact (Nat.Prime p)] in
theorem prepareZero_quotient (c : Fin 4 → ZMod (p^μ)) :
    quotientDenote c ((prepareZero p μ).1.map (wordValue p μ)) = 0 := by
  simp only [prepareZero, Quad.map, literalWordRun_zero, quotientDenote_const, map_zero]

omit [Fact (Nat.Prime p)] in
theorem prepareOne_quotient (hμ : 0 < μ) (c : Fin 4 → ZMod (p^μ)) :
    quotientDenote c ((prepareOne p μ).1.map (wordValue p μ)) = 1 := by
  simp only [prepareOne, Quad.map, literalWordRun_zero, literalWordRun_one p μ hμ,
    quotientDenote_const, map_one]

variable (M : Modulus p μ)

def wordAdd (x y : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let r := addBaseRun (baseWidth p μ) M.bits x.val y.val
  (⟨r.1, addBaseRun_length _ _ _ _⟩, r.2)

def wordMul (x y : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let r := mulBaseRun (baseWidth p μ) M.bits x.val y.val
  (⟨r.1, mulBaseRun_length _ _ _ _⟩, r.2)

theorem wordAdd_correct (x y : Word (baseWidth p μ)) :
    wordValue p μ (wordAdd p μ M x y).1 = wordValue p μ x + wordValue p μ y := by
  unfold wordValue wordAdd
  dsimp only
  rw [addBaseRun_value]
  · simp only [M.value, ZMod.natCast_mod, Nat.cast_add]
  · rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos μ
  · rw [M.value]; exact modulus_le_width p μ

theorem wordMul_correct (x y : Word (baseWidth p μ)) :
    wordValue p μ (wordMul p μ M x y).1 = wordValue p μ x * wordValue p μ y := by
  unfold wordValue wordMul
  dsimp only
  rw [mulBaseRun_value]
  · simp only [M.value, ZMod.natCast_mod, Nat.cast_mul]
  · rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos μ
  · rw [M.value]; exact modulus_le_width p μ

omit [Fact (Nat.Prime p)] in
theorem wordAdd_cost (x y : Word (baseWidth p μ)) :
    (wordAdd p μ M x y).2 ≤ scalarBudget p μ := by
  have h := addBaseRun_cost (baseWidth p μ) M.bits x.val y.val M.length_le
    (by rw [x.property]) (by rw [y.property])
  change (addBaseRun _ _ _ _).2 ≤ _
  exact h.trans (by unfold scalarBudget; omega)

omit [Fact (Nat.Prime p)] in
theorem wordMul_cost (x y : Word (baseWidth p μ)) :
    (wordMul p μ M x y).2 ≤ scalarBudget p μ :=
  mulBaseRun_cost (baseWidth p μ) M.bits x.val y.val M.length_le
    (by rw [x.property]) (by rw [y.property])

theorem wordAdd_canonical (x y : Word (baseWidth p μ)) :
    BinaryArithmetic.toNat (wordAdd p μ M x y).1.val < p^μ := by
  change BinaryArithmetic.toNat (addBaseRun _ _ _ _).1 < _
  rw [addBaseRun_value _ _ _ _ (by
    rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos μ) (by
    rw [M.value]; exact modulus_le_width p μ), M.value]
  exact Nat.mod_lt _ (pow_pos (Fact.out : p.Prime).pos μ)

/-- A stored zero word avoids computing any residue representation inside
the negation callback. -/
def zeroWord : Word (baseWidth p μ) :=
  ⟨List.replicate (baseWidth p μ) false, by simp⟩

omit [Fact (Nat.Prime p)] in
@[simp] theorem zeroWord_value : wordValue p μ (zeroWord p μ) = 0 := by
  have hz (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, toNat_cons, bitVal_false, ih]
  simp [wordValue, zeroWord, hz]

def wordNeg (x : Word (baseWidth p μ)) : Word (baseWidth p μ) × ℕ :=
  let reduced := wordAdd p μ M x (zeroWord p μ)
  let r := SubexpBaseNegation.negBaseRun (baseWidth p μ) M.bits reduced.1.val
  (⟨r.1, SubexpBaseNegation.negBaseRun_length _ _ _⟩,
    baseWidth p μ + reduced.2 + r.2)

theorem wordNeg_correct (x : Word (baseWidth p μ)) :
    wordValue p μ (wordNeg p μ M x).1 = -wordValue p μ x := by
  have h := SubexpBaseNegation.negBaseRun_cast (baseWidth p μ) M.bits
    (wordAdd p μ M x (zeroWord p μ)).1.val M.length_le
    (by rw [(wordAdd p μ M x (zeroWord p μ)).1.property])
    (by rw [M.value]; exact pow_pos (Fact.out : p.Prime).pos μ)
    (by rw [M.value]; exact modulus_le_width p μ)
    (by rw [M.value]; exact wordAdd_canonical p μ M x (zeroWord p μ))
  rw [M.value] at h
  change wordValue p μ (wordNeg p μ M x).1 =
    -wordValue p μ (wordAdd p μ M x (zeroWord p μ)).1 at h
  simpa only [wordAdd_correct, zeroWord_value, add_zero] using h

omit [Fact (Nat.Prime p)] in
theorem wordNeg_cost (x : Word (baseWidth p μ)) :
    (wordNeg p μ M x).2 ≤ scalarBudget p μ := by
  have ha := addBaseRun_cost (baseWidth p μ) M.bits x.val (zeroWord p μ).val
    M.length_le (by rw [x.property]) (by rw [(zeroWord p μ).property])
  have hn := SubexpBaseNegation.negBaseRun_cost (baseWidth p μ) M.bits
    (wordAdd p μ M x (zeroWord p μ)).1.val M.length_le
  change baseWidth p μ + (wordAdd p μ M x (zeroWord p μ)).2 +
    (SubexpBaseNegation.negBaseRun _ _ _).2 ≤ _
  change (wordAdd p μ M x (zeroWord p μ)).2 ≤ _ at ha
  unfold scalarBudget
  nlinarith [sq_nonneg (baseWidth p μ)]

def binaryAdd (a b : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) × ℕ :=
  addRun (wordAdd p μ M) a b

def binaryMul (t a b : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) × ℕ :=
  mulRun (wordAdd p μ M) (wordMul p μ M) t a b

def binaryNeg (a : Quad (Word (baseWidth p μ))) : Quad (Word (baseWidth p μ)) × ℕ :=
  let r0 := wordNeg p μ M a.c0
  let r1 := wordNeg p μ M a.c1
  let r2 := wordNeg p μ M a.c2
  let r3 := wordNeg p μ M a.c3
  (⟨r0.1, r1.1, r2.1, r3.1⟩, r0.2 + r1.2 + r2.2 + r3.2)

theorem binaryAdd_correct (a b : Quad (Word (baseWidth p μ))) :
    ((binaryAdd p μ M a b).1).map (wordValue p μ) =
      add (a.map (wordValue p μ)) (b.map (wordValue p μ)) :=
  addRun_correct (wordValue p μ) (wordAdd p μ M) (wordAdd_correct p μ M) a b

theorem binaryMul_correct (t a b : Quad (Word (baseWidth p μ))) :
    ((binaryMul p μ M t a b).1).map (wordValue p μ) =
      mul (t.map (wordValue p μ)) (a.map (wordValue p μ)) (b.map (wordValue p μ)) :=
  mulRun_correct (wordValue p μ) (wordAdd p μ M) (wordMul p μ M)
    (wordAdd_correct p μ M) (wordMul_correct p μ M) t a b

theorem binaryNeg_correct (a : Quad (Word (baseWidth p μ))) :
    ((binaryNeg p μ M a).1).map (wordValue p μ) = (a.map (wordValue p μ)).map Neg.neg := by
  simp [binaryNeg, Quad.map, wordNeg_correct]

omit [Fact (Nat.Prime p)] in
theorem binaryAdd_cost (a b : Quad (Word (baseWidth p μ))) :
    (binaryAdd p μ M a b).2 ≤ 4 * scalarBudget p μ :=
  addRun_cost (wordAdd p μ M) (scalarBudget p μ) (wordAdd_cost p μ M) a b

omit [Fact (Nat.Prime p)] in
theorem binaryMul_cost (t a b : Quad (Word (baseWidth p μ))) :
    (binaryMul p μ M t a b).2 ≤ 49 * scalarBudget p μ :=
  mulRun_cost (wordAdd p μ M) (wordMul p μ M) (scalarBudget p μ)
    (wordAdd_cost p μ M) (wordMul_cost p μ M) t a b

omit [Fact (Nat.Prime p)] in
theorem binaryNeg_cost (a : Quad (Word (baseWidth p μ))) :
    (binaryNeg p μ M a).2 ≤ 4 * scalarBudget p μ := by
  have h0 := wordNeg_cost p μ M a.c0
  have h1 := wordNeg_cost p μ M a.c1
  have h2 := wordNeg_cost p μ M a.c2
  have h3 := wordNeg_cost p μ M a.c3
  dsimp [binaryNeg]
  omega

theorem binaryAdd_quotient (c : Fin 4 → ZMod (p^μ))
    (a b : Quad (Word (baseWidth p μ))) :
    quotientDenote c (((binaryAdd p μ M a b).1).map (wordValue p μ)) =
      quotientDenote c (a.map (wordValue p μ)) + quotientDenote c (b.map (wordValue p μ)) := by
  rw [binaryAdd_correct, quotientDenote_add]

theorem binaryMul_quotient (c : Fin 4 → ZMod (p^μ))
    (t a b : Quad (Word (baseWidth p μ)))
    (ht : t.map (wordValue p μ) = reductionData c) :
    quotientDenote c (((binaryMul p μ M t a b).1).map (wordValue p μ)) =
      quotientDenote c (a.map (wordValue p μ)) * quotientDenote c (b.map (wordValue p μ)) := by
  rw [binaryMul_correct, ht, quotientDenote_mul]

theorem binaryNeg_quotient (c : Fin 4 → ZMod (p^μ))
    (a : Quad (Word (baseWidth p μ))) :
    quotientDenote c (((binaryNeg p μ M a).1).map (wordValue p μ)) =
      -quotientDenote c (a.map (wordValue p μ)) := by
  rw [binaryNeg_correct, quotientDenote_neg]

/-- Prepare the reduction cache by an actual binary negation of the four
already encoded coefficients. Its setup cost is charged once. -/
def prepareReduction (coefficients : Quad (Word (baseWidth p μ))) :
    Quad (Word (baseWidth p μ)) × ℕ := binaryNeg p μ M coefficients

theorem prepareReduction_correct (c : Fin 4 → ZMod (p^μ))
    (coefficients : Quad (Word (baseWidth p μ)))
    (hc : coefficients.map (wordValue p μ) = Quad.ofFn c) :
    ((prepareReduction p μ M coefficients).1).map (wordValue p μ) = reductionData c := by
  rw [prepareReduction, binaryNeg_correct, hc]
  rfl

omit [Fact (Nat.Prime p)] in
theorem prepareReduction_cost (coefficients : Quad (Word (baseWidth p μ))) :
    (prepareReduction p μ M coefficients).2 ≤ 4 * scalarBudget p μ :=
  binaryNeg_cost p μ M coefficients

end SubexponentialSAT.SubexpPreparedQuartic

end OAI.Algorithms
