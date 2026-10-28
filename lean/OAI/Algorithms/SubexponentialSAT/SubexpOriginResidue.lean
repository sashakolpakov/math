import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorRowCorrectness

namespace OAI.Algorithms

/-! Source-field origins obtained from the current-node Taylor constant
terms. Every coordinate is reduced modulo p before restoring source width;
discarding high bits alone would not implement the residue map. -/

namespace SubexponentialSAT.SubexpOriginResidue

open BinaryArithmetic SubexpLiftRing SubexpQuarticRing

def bits (width modulus input : List Bool) : List Bool :=
  ModularArithmetic.padTo width (ModularArithmetic.reduce modulus input)

@[simp] theorem bits_length (width modulus input : List Bool) :
    (bits width modulus input).length = width.length :=
  ModularArithmetic.padTo_length _ _

theorem bits_value (width modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hc : BinaryArithmetic.toNat modulus ≤ 2 ^ width.length) :
    BinaryArithmetic.toNat (bits width modulus input) = BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus := by
  rw [bits, ModularRingPrograms.padTo_value_of_lt]
  · exact ModularArithmetic.reduce_correct modulus input hm
  · rw [ModularArithmetic.reduce_correct modulus input hm]
    exact (Nat.mod_lt _ hm).trans_le hc

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length = baseWidth p 1)

def word {B : ℕ} (input : Word B) : Word (baseWidth p 1) :=
  ⟨bits width M.bits input.val, (bits_length _ _ _).trans hw⟩

theorem word_value {B : ℕ} (input : Word B) :
    BinaryArithmetic.toNat (word p M width hw input).val = BinaryArithmetic.toNat input.val % p := by
  have hm : BinaryArithmetic.toNat M.bits = p := by simpa using M.value
  change BinaryArithmetic.toNat (bits width M.bits input.val) = _
  rw [bits_value width M.bits input.val (by rw [hm]; exact (Fact.out : p.Prime).pos)
    (by rw [hm, hw]; simpa using modulus_le_width p 1), hm]

theorem word_sourceValue {B : ℕ} (input : Word B) :
    SubexpWordLift.sourceValue p (word p M width hw input) = (BinaryArithmetic.toNat input.val : ZMod p) := by
  rw [SubexpWordLift.sourceValue, word_value, ZMod.natCast_mod]

def quad {B : ℕ} (input : Quad (Word B)) : Quad (Word (baseWidth p 1)) :=
  input.map (word p M width hw)

theorem quad_decode (μ : ℕ) (hμ : 0 < μ)
    (source : SubexpSelectedConversions.Prepared p 0)
    (input : Quad (Word (baseWidth p μ))) :
    source.residueRing.decode (quad p M width hw input) =
      SubexpActualRing.rho p μ hμ
        (SubexpHornerMachine.decode p μ (QuarticSearch.liftedCoefficients p μ) input) := by
  rw [SubexpSelectedConversions.Prepared.residueRing_decode]
  change _ = SubexpActualRing.rho p μ hμ
    (quotientDenote (QuarticSearch.liftedCoefficients p μ) (input.map (wordValue p μ)))
  rw [SubexpSelectedConversions.rho_quotientDenote]
  congr 1
  cases input
  simp only [quad, Quad.map, word_sourceValue, wordValue, map_natCast]

/-- A source row's origin is its evaluation at the current node. The
constant coefficient is read only after the complete Taylor shift. -/
theorem rho_shift_zero (μ : ℕ) (hμ : 0 < μ)
    (R : ℕ) (f : Polynomial (SubexpActualRing.E p))
    (hf : f.natDegree ≤ R) (theta : SubexpActualRing.Ring p μ) :
    SubexpActualRing.rho p μ hμ
      (((SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R f).comp
        (Polynomial.X + Polynomial.C theta)).coeff 0) =
      f.eval (SubexpActualRing.rho p μ hμ theta) := by
  let rho := SubexpActualRing.rho p μ hμ
  let lifted := SubexpExplicitLift.liftPolynomial (SubexpActualRing.sectionValue p μ hμ) R f
  have hmap : lifted.map rho = f :=
    SubexpExplicitLift.map_liftPolynomial rho (SubexpActualRing.sectionValue p μ hμ)
      (SubexpActualRing.sectionValue_zero p μ hμ)
      (SubexpActualRing.rho_sectionValue p μ hμ) R f hf
  change rho ((lifted.comp (Polynomial.X + Polynomial.C theta)).coeff 0) = _
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add]
  calc
    rho (lifted.eval theta) = (lifted.map rho).eval (rho theta) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    _ = f.eval (rho theta) := by rw [hmap]

theorem shifted_entry_origin (μ : ℕ) (hμ : 0 < μ)
    (source : SubexpSelectedConversions.Prepared p 0)
    (target : SubexpPreparedQuartic.Modulus p μ)
    (reduction theta : SubexpTaylorRow.Code p μ)
    (hreduction : reduction.map (wordValue p μ) =
      reductionData (QuarticSearch.liftedCoefficients p μ))
    (R N : ℕ) (hN : 0 < N) (e : SubexpTaylorRowCorrectness.RowExpr p)
    (hdegree : ((e.map (SubexpRowSourceSemantics.denote source)).eval).natDegree ≤ R) :
    source.residueRing.decode (quad p M width hw
      (SubexpTaylorRowCorrectness.entry p μ source target reduction theta R N e ⟨0, hN⟩)) =
      ((e.map (SubexpRowSourceSemantics.denote source)).eval).eval
        (SubexpActualRing.rho p μ hμ
          (SubexpHornerMachine.decode p μ (QuarticSearch.liftedCoefficients p μ) theta)) := by
  rw [quad_decode p M width hw μ hμ source,
    SubexpTaylorRowCorrectness.entry_eq p μ source target reduction theta hμ
      hreduction R N e hdegree]
  exact rho_shift_zero p μ hμ R _ hdegree _

end SubexponentialSAT.SubexpOriginResidue

end OAI.Algorithms
