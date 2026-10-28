import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic
import OAI.Algorithms.SubexponentialSAT.SubexpFieldNodes

namespace OAI.Algorithms

/-!
# Direct lifting of encoded residue-field coefficients

Each input coefficient is reduced modulo p and zero-padded to the target
prime-power width. The data path never decodes an abstract quotient field
element or chooses a preimage. Four such operations implement the explicit
coordinate section of the selected quartic extension.
-/

namespace SubexponentialSAT.SubexpWordLift

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime]

def sourceValue (x : Word (baseWidth p 1)) : ZMod p := (BinaryArithmetic.toNat x.val : ℕ)

/-- The source modulus p is already prepared input data. -/
def liftWordRun (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (x : Word (baseWidth p 1)) : Word (baseWidth p μ) × ℕ :=
  let reduced := ModularArithmetic.reduceLogged sourceModulus.bits x.val
  let padded := SubexpModulusConstruction.normalizeRun (baseWidth p μ) reduced.1
  (⟨padded.1, SubexpModulusConstruction.normalizeRun_length _ _⟩,
    reduced.2.length + padded.2.length)

theorem liftWordRun_raw (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (x : Word (baseWidth p 1)) :
    BinaryArithmetic.toNat (liftWordRun p μ sourceModulus x).1.val = (sourceValue p x).val := by
  have hm : BinaryArithmetic.toNat sourceModulus.bits = p := by simpa using sourceModulus.value
  have hpos : 0 < BinaryArithmetic.toNat sourceModulus.bits := by rw [hm]; exact (Fact.out : p.Prime).pos
  have hred := ModularArithmetic.reduceLogged_correct sourceModulus.bits x.val hpos
  rw [hm] at hred
  change BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ _).1 = _
  rw [SubexpModulusConstruction.normalizeRun_value]
  · simpa only [sourceValue, ZMod.val_natCast] using hred
  · rw [hred]
    exact (Nat.mod_lt _ (Fact.out : p.Prime).pos).trans_le
      ((Nat.le_pow hμ).trans (modulus_le_width p μ))

theorem liftWordRun_correct (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (x : Word (baseWidth p 1)) :
    wordValue p μ (liftWordRun p μ sourceModulus x).1 =
      ((sourceValue p x).val : ZMod (p^μ)) := by
  unfold wordValue
  rw [liftWordRun_raw p μ sourceModulus hμ x]

def liftBudget : ℕ :=
  3 * (baseWidth p 1 + 1) * (baseWidth p 1 + 1) + 4 * (baseWidth p 1 + 1) +
    (3 * baseWidth p μ + 1)

omit [Fact p.Prime] in
theorem liftWordRun_cost (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (x : Word (baseWidth p 1)) :
    (liftWordRun p μ sourceModulus x).2 ≤ liftBudget p μ := by
  have hr := ModularArithmetic.reduceLogged_count_le sourceModulus.bits x.val
    (baseWidth p 1 + 1) sourceModulus.length_le (by rw [x.property]; omega)
  simpa only [liftWordRun, SubexpModulusConstruction.normalizeRun_cost, liftBudget] using
    Nat.add_le_add_right hr (3 * baseWidth p μ + 1)

def liftQuadRun (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (a : Quad (Word (baseWidth p 1))) : Quad (Word (baseWidth p μ)) × ℕ :=
  let a0 := liftWordRun p μ sourceModulus a.c0
  let a1 := liftWordRun p μ sourceModulus a.c1
  let a2 := liftWordRun p μ sourceModulus a.c2
  let a3 := liftWordRun p μ sourceModulus a.c3
  (⟨a0.1, a1.1, a2.1, a3.1⟩, a0.2 + a1.2 + a2.2 + a3.2)

theorem liftQuadRun_correct (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (a : Quad (Word (baseWidth p 1))) :
    ((liftQuadRun p μ sourceModulus a).1).map (wordValue p μ) =
      (a.map (sourceValue p)).map (fun z : ZMod p => (z.val : ZMod (p^μ))) := by
  simp [liftQuadRun, Quad.map, liftWordRun_correct p μ sourceModulus hμ]

omit [Fact p.Prime] in
theorem liftQuadRun_cost (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (a : Quad (Word (baseWidth p 1))) :
    (liftQuadRun p μ sourceModulus a).2 ≤ 4 * liftBudget p μ := by
  have h0 := liftWordRun_cost p μ sourceModulus a.c0
  have h1 := liftWordRun_cost p μ sourceModulus a.c1
  have h2 := liftWordRun_cost p μ sourceModulus a.c2
  have h3 := liftWordRun_cost p μ sourceModulus a.c3
  dsimp [liftQuadRun]
  omega

/-- The implemented four-word conversion is exactly the chosen coordinate
section, including for unreduced source words. -/
theorem liftQuadRun_section (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (a : Quad (Word (baseWidth p 1))) :
    quotientDenote (QuarticSearch.liftedCoefficients p μ)
      (((liftQuadRun p μ sourceModulus a).1).map (wordValue p μ)) =
      SubexpActualRing.sectionValue p μ hμ
        (quotientDenote (QuarticSearch.coefficients p) (a.map (sourceValue p))) := by
  rw [liftQuadRun_correct p μ sourceModulus hμ a]
  have hl : (a.map (sourceValue p)).map (fun z : ZMod p => (z.val : ZMod (p^μ))) =
      SubexpFieldNodes.liftQuad p μ (Quad.toFn (a.map (sourceValue p))) := by
    cases a
    rfl
  rw [hl, SubexpFieldNodes.quotientDenote_liftQuad p μ hμ]
  congr 1
  rw [← SubexpFieldNodes.quotientDenote_ofFn]
  congr 1

/-- Copy the input word and construct three zero words. Each of the four
normalization passes contributes its explicit source-event count. -/
def constantRun (x : Word (baseWidth p μ)) : Quad (Word (baseWidth p μ)) × ℕ :=
  let a := SubexpPreparedQuartic.literalWordRun p μ x.val
  let b := SubexpPreparedQuartic.literalWordRun p μ []
  let c := SubexpPreparedQuartic.literalWordRun p μ []
  let d := SubexpPreparedQuartic.literalWordRun p μ []
  (⟨a.1, b.1, c.1, d.1⟩, a.2 + b.2 + c.2 + d.2)

omit [Fact p.Prime] in
theorem constantRun_cost (x : Word (baseWidth p μ)) :
    (constantRun p μ x).2 = 12 * baseWidth p μ + 4 := by
  simp only [constantRun, SubexpPreparedQuartic.literalWordRun_cost]
  omega

omit [Fact p.Prime] in
private theorem copiedWord_raw (x : Word (baseWidth p μ)) :
    BinaryArithmetic.toNat (SubexpPreparedQuartic.literalWordRun p μ x.val).1.val = BinaryArithmetic.toNat x.val := by
  apply SubexpModulusConstruction.normalizeRun_value
  simpa only [x.property] using ModularArithmetic.toNat_lt_pow_length x.val

omit [Fact p.Prime] in
private theorem zeroWord_raw :
    BinaryArithmetic.toNat (SubexpPreparedQuartic.literalWordRun p μ []).1.val = 0 := by
  change BinaryArithmetic.toNat (SubexpModulusConstruction.normalizeRun _ []).1 = 0
  rw [SubexpModulusConstruction.normalizeRun_value]
  · rfl
  · exact Nat.two_pow_pos _

omit [Fact p.Prime] in
theorem constantRun_map (x : Word (baseWidth p μ)) :
    (constantRun p μ x).1.map (wordValue p μ) = ⟨wordValue p μ x, 0, 0, 0⟩ := by
  simp only [constantRun, Quad.map, wordValue, copiedWord_raw, zeroWord_raw,
    Nat.cast_zero]

/-- Embed one encoded prime-field coordinate into the selected residue field.
This routine never extracts a value from an abstract field element. -/
def embedRun (x : Word (baseWidth p 1)) : Quad (Word (baseWidth p 1)) × ℕ :=
  constantRun p 1 x

omit [Fact p.Prime] in
theorem embedRun_cost (x : Word (baseWidth p 1)) :
    (embedRun p x).2 = 12 * baseWidth p 1 + 4 := constantRun_cost p 1 x

theorem embedRun_correct (x : Word (baseWidth p 1)) :
    quotientDenote (QuarticSearch.coefficients p)
      ((embedRun p x).1.map (sourceValue p)) =
      algebraMap (ZMod p) (SubexpActualRing.E p) (sourceValue p x) := by
  simp only [embedRun, constantRun, Quad.map, sourceValue, copiedWord_raw,
    zeroWord_raw, Nat.cast_zero, quotientDenote_const]
  rfl

/-- Lift a scalar coordinate and marshal it as a constant quartic coefficient.
Both modular reduction and the four output-word passes are executed. -/
def liftScalarRun (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (x : Word (baseWidth p 1)) : Quad (Word (baseWidth p μ)) × ℕ :=
  let lifted := liftWordRun p μ sourceModulus x
  let out := constantRun p μ lifted.1
  (out.1, lifted.2 + out.2)

omit [Fact p.Prime] in
theorem liftScalarRun_cost (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (x : Word (baseWidth p 1)) :
    (liftScalarRun p μ sourceModulus x).2 ≤
      liftBudget p μ + 12 * baseWidth p μ + 4 := by
  have h := liftWordRun_cost p μ sourceModulus x
  simp only [liftScalarRun, constantRun_cost]
  omega

theorem liftScalarRun_correct (sourceModulus : SubexpPreparedQuartic.Modulus p 1)
    (hμ : 0 < μ) (x : Word (baseWidth p 1)) :
    quotientDenote (QuarticSearch.liftedCoefficients p μ)
      ((liftScalarRun p μ sourceModulus x).1.map (wordValue p μ)) =
      SubexpActualRing.coordinateLift p μ (sourceValue p x) := by
  simp only [liftScalarRun, constantRun_map,
    liftWordRun_correct p μ sourceModulus hμ, quotientDenote_const,
    map_natCast, SubexpActualRing.coordinateLift]
  exact map_natCast (LiftRing.of (SubexpActualRing.F p μ)) (sourceValue p x).val

end SubexponentialSAT.SubexpWordLift

end OAI.Algorithms
