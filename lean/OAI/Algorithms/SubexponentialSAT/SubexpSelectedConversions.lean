import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWordLift
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Concrete conversions for the selected quartic counting interface

The residue implementation is the prepared prime-power implementation at
exponent one, with only its specification decoder postcomposed by reduction.
The runtime callbacks stay unchanged. Beta lifting runs four explicit
remainder-and-padding operations, including for unreduced source words.

Coordinate encoding below is a value-level adapter for a typed `ZMod p`
coordinate. It uses the integer representative and fixed-width binary
encoding, never extraction from an abstract quotient. This module does not
claim a primitive-machine implementation of that adapter.
-/

namespace SubexponentialSAT.SubexpSelectedConversions

open SubexpSymbolicCost SubexpQuarticRing SubexpLiftRing

/-- Prepared runtime data with the exact initialization facts needed by its
semantic interpretation. These are local cache facts, not solver outputs. -/
structure Prepared (p D : ℕ) [Fact p.Prime] where
  modulus : SubexpPreparedQuartic.Modulus p (D + 1)
  reduction : QuarticCode p D
  zero : QuarticCode p D
  one : QuarticCode p D
  reduction_spec : reduction.map (wordValue p (D + 1)) =
    reductionData (QuarticSearch.liftedCoefficients p (D + 1))
  zero_spec : quotientDenote (QuarticSearch.liftedCoefficients p (D + 1))
    (zero.map (wordValue p (D + 1))) = 0
  one_spec : quotientDenote (QuarticSearch.liftedCoefficients p (D + 1))
    (one.map (wordValue p (D + 1))) = 1

variable {p D : ℕ} [Fact p.Prime]

private theorem map_denote {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (x : S) (a : Quad R) :
    g (denote f x a) = denote (g.comp f) (g x) a := by
  simp only [denote, map_add, map_mul, map_pow, RingHom.comp_apply]

def Prepared.program (data : Prepared p D) : RingProgram (QuarticCode p D) :=
  preparedProgram p D data.modulus data.reduction data.zero data.one

noncomputable def Prepared.ring (data : Prepared p D) :
    RepresentedRing (QuarticCode p D) (SubexpActualRing.Ring p (D + 1)) :=
  preparedRing p D data.modulus (QuarticSearch.liftedCoefficients p (D + 1))
    data.reduction data.zero data.one data.reduction_spec data.zero_spec data.one_spec

@[simp] theorem Prepared.ring_program (data : Prepared p D) :
    data.ring.program = data.program := rfl

@[simp] theorem Prepared.ring_decode (data : Prepared p D) (a : QuarticCode p D) :
    data.ring.decode a = quotientDenote (QuarticSearch.liftedCoefficients p (D + 1))
      (a.map (wordValue p (D + 1))) := rfl

/-- Reinterpret the exponent-one quotient as the selected residue field.
No operation or runtime counter is changed. -/
noncomputable def Prepared.residueRing (data : Prepared p 0) :
    RepresentedRing (QuarticCode p 0) (SubexpActualRing.E p) :=
  data.ring.map (SubexpActualRing.rho p 1 (by decide))

@[simp] theorem Prepared.residueRing_program (data : Prepared p 0) :
    data.residueRing.program = data.program := rfl

/-- Reduction of the quartic value is coefficientwise reduction, in the
same selected residue polynomial. No field-cardinality identification occurs. -/
theorem rho_quotientDenote (μ : ℕ) (hμ : 0 < μ) (a : Quad (ZMod (p ^ μ))) :
    SubexpActualRing.rho p μ hμ
      (quotientDenote (QuarticSearch.liftedCoefficients p μ) a) =
      quotientDenote (QuarticSearch.coefficients p)
        (a.map (LiftRing.baseReduction p μ hμ)) := by
  have hr (q : Polynomial (ZMod (p ^ μ))) :
      SubexpActualRing.rho p μ hμ
          (LiftRing.mk (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ)) q) =
        LiftRing.mk (QuarticSearch.poly (QuarticSearch.coefficients p))
          (q.map (LiftRing.baseReduction p μ hμ)) :=
    SubexpActualRing.rho_mk p μ hμ q
  have hcoeff :
      (SubexpActualRing.rho p μ hμ).comp
          (LiftRing.of (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ))) =
        (LiftRing.of (QuarticSearch.poly (QuarticSearch.coefficients p))).comp
          (LiftRing.baseReduction p μ hμ) := by
    ext x
    change SubexpActualRing.rho p μ hμ
        (LiftRing.mk (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ))
          (Polynomial.C x)) =
        LiftRing.mk (QuarticSearch.poly (QuarticSearch.coefficients p))
          (Polynomial.C (LiftRing.baseReduction p μ hμ x))
    rw [hr, Polynomial.map_C]
  have hroot : SubexpActualRing.rho p μ hμ
      (LiftRing.mk (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ)) Polynomial.X) =
        LiftRing.mk (QuarticSearch.poly (QuarticSearch.coefficients p)) Polynomial.X := by
    simpa only [Polynomial.map_X] using hr Polynomial.X
  unfold quotientDenote
  calc
    _ = denote
        ((SubexpActualRing.rho p μ hμ).comp
          (LiftRing.of (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ))))
        (SubexpActualRing.rho p μ hμ
          (LiftRing.mk (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ))
            Polynomial.X)) a :=
      map_denote
        (LiftRing.of (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ)))
        (SubexpActualRing.rho p μ hμ)
        (LiftRing.mk (QuarticSearch.poly (QuarticSearch.liftedCoefficients p μ))
          Polynomial.X) a
    _ = _ := by
      rw [hcoeff, hroot]
      rfl

/-- Exact decoder bridge for source code words, without a canonicality
assumption on their contents. -/
theorem Prepared.residueRing_decode (data : Prepared p 0) (a : QuarticCode p 0) :
    data.residueRing.decode a = quotientDenote (QuarticSearch.coefficients p)
      (a.map (SubexpWordLift.sourceValue p)) := by
  change SubexpActualRing.rho p 1 (by decide)
    (quotientDenote (QuarticSearch.liftedCoefficients p 1)
      (a.map (wordValue p 1))) = _
  rw [rho_quotientDenote]
  congr 1
  cases a
  simp only [Quad.map, wordValue, SubexpWordLift.sourceValue, map_natCast]

/-- Encode a typed prime-field coordinate by four explicit binary words. -/
def coordinateCode (D : ℕ) (z : ZMod p) : QuarticCode p D :=
  binaryConst p (D + 1) (z.val : ZMod (p ^ (D + 1)))

theorem coordinateCode_decode (data : Prepared p D) (z : ZMod p) :
    data.ring.decode (coordinateCode D z) = SubexpActualRing.coordinateLift p (D + 1) z := by
  rw [Prepared.ring_decode, coordinateCode, binaryConst_quotient]
  exact map_natCast _ _

theorem coordinateCode_residue (data : Prepared p 0) (z : ZMod p) :
    data.residueRing.decode (coordinateCode 0 z) =
      algebraMap (ZMod p) (SubexpActualRing.E p) z := by
  change SubexpActualRing.rho p 1 (by decide)
    (data.ring.decode (coordinateCode 0 z)) = _
  rw [coordinateCode_decode]
  exact SubexpActualRing.rho_coordinateLift p 1 (by decide) z

/-- The runtime beta conversion uses only the already prepared modulus p
and the four source coefficient words. -/
def betaLift (source : Prepared p 0) (D : ℕ) (a : QuarticCode p 0) : QuarticCode p D :=
  (SubexpWordLift.liftQuadRun p (D + 1) source.modulus a).1

theorem betaLift_decode (source : Prepared p 0) (target : Prepared p D)
    (a : QuarticCode p 0) :
    target.ring.decode (betaLift source D a) =
      (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
        (source.residueRing.decode a) := by
  rw [Prepared.ring_decode, Prepared.residueRing_decode]
  exact SubexpWordLift.liftQuadRun_section p (D + 1) source.modulus (Nat.succ_pos D) a

/-- Fixed-width representation of a typed coordinate. Runtime producers that
already have this word can use `embedRun` and `liftScalarRun` directly. -/
def labelWord (z : ZMod p) : Word (baseWidth p 1) :=
  encodeWord p 1 (z.val : ZMod (p ^ 1))

@[simp] theorem labelWord_value (z : ZMod p) :
    SubexpWordLift.sourceValue p (labelWord z) = z := by
  change ((BinaryArithmetic.toNat (encodeBase p 1 (z.val : ZMod (p ^ 1))) : ℕ) : ZMod p) = z
  rw [encodeBase_value, ZMod.val_natCast, pow_one, Nat.mod_eq_of_lt z.val_lt]
  exact ZMod.natCast_zmod_val z

def embedCode (z : ZMod p) : QuarticCode p 0 :=
  (SubexpWordLift.embedRun p (labelWord z)).1

def weightCode (source : Prepared p 0) (D : ℕ) (z : ZMod p) : QuarticCode p D :=
  (SubexpWordLift.liftScalarRun p (D + 1) source.modulus (labelWord z)).1

theorem embedRun_decode (source : Prepared p 0) (x : Word (baseWidth p 1)) :
    source.residueRing.decode (SubexpWordLift.embedRun p x).1 =
      algebraMap (ZMod p) (SubexpActualRing.E p) (SubexpWordLift.sourceValue p x) := by
  rw [Prepared.residueRing_decode]
  exact SubexpWordLift.embedRun_correct p x

theorem embedCode_decode (source : Prepared p 0) (z : ZMod p) :
    source.residueRing.decode (embedCode z) =
      algebraMap (ZMod p) (SubexpActualRing.E p) z := by
  rw [embedCode, embedRun_decode, labelWord_value]

theorem liftScalarRun_decode (source : Prepared p 0) (target : Prepared p D)
    (x : Word (baseWidth p 1)) :
    target.ring.decode (SubexpWordLift.liftScalarRun p (D + 1) source.modulus x).1 =
      SubexpActualRing.coordinateLift p (D + 1) (SubexpWordLift.sourceValue p x) := by
  rw [Prepared.ring_decode]
  exact SubexpWordLift.liftScalarRun_correct p (D + 1) source.modulus (Nat.succ_pos D) x

theorem weightCode_decode (source : Prepared p 0) (target : Prepared p D) (z : ZMod p) :
    target.ring.decode (weightCode source D z) =
      SubexpActualRing.coordinateLift p (D + 1) z := by
  rw [weightCode, liftScalarRun_decode, labelWord_value]

/-- The three conversion facts expected by `SelectedInput`, all derived
from the concrete encodings and the prepared local arithmetic. -/
theorem conversion_laws (source : Prepared p 0) (target : Prepared p D) :
    (∀ z, source.residueRing.decode (embedCode z) =
      algebraMap (ZMod p) (SubexpActualRing.E p) z) ∧
    (∀ a, target.ring.decode (betaLift source D a) =
      (SubexpActualRing.residueSection p (D + 1) (Nat.succ_pos D)).lift
        (source.residueRing.decode a)) ∧
    (∀ z, target.ring.decode (weightCode source D z) =
      SubexpActualRing.coordinateLift p (D + 1) z) :=
  ⟨embedCode_decode source, betaLift_decode source target, weightCode_decode source target⟩

/-- Actual selected quartic coefficients, encoded without quotient extraction. -/
def selectedCoefficientCode (p D : ℕ) [Fact p.Prime] : QuarticCode p D :=
  (Quad.ofFn (QuarticSearch.liftedCoefficients p (D + 1))).map (encodeWord p (D + 1))

theorem selectedCoefficientCode_decode :
    (selectedCoefficientCode p D).map (wordValue p (D + 1)) =
      Quad.ofFn (QuarticSearch.liftedCoefficients p (D + 1)) := by
  simp [selectedCoefficientCode, Quad.map, Quad.ofFn]

/-- Run the published binary initializer and certify its resulting caches.
The only supplied facts identify the input prime word and its width. -/
def initializeSelected (p D : ℕ) [Fact p.Prime] (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) : Prepared p D :=
  let M := (SubexpPreparedQuartic.prepareModulus p (D + 1) primeBits hvalue hwidth).1
  let coefficients := selectedCoefficientCode p D
  { modulus := M
    reduction := (SubexpPreparedQuartic.prepareReduction p (D + 1) M coefficients).1
    zero := (SubexpPreparedQuartic.prepareZero p (D + 1)).1
    one := (SubexpPreparedQuartic.prepareOne p (D + 1)).1
    reduction_spec := SubexpPreparedQuartic.prepareReduction_correct p (D + 1) M
      (QuarticSearch.liftedCoefficients p (D + 1)) coefficients selectedCoefficientCode_decode
    zero_spec := SubexpPreparedQuartic.prepareZero_quotient p (D + 1) _
    one_spec := SubexpPreparedQuartic.prepareOne_quotient p (D + 1) (Nat.succ_pos D) _ }

theorem initializeSelected_program (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) :
    (initializeSelected p D primeBits hvalue hwidth).program =
      (initializeQuartic p D primeBits hvalue hwidth (selectedCoefficientCode p D)).1.program := rfl

theorem initializeSelected_ring (primeBits : List Bool)
    (hvalue : BinaryArithmetic.toNat primeBits = p)
    (hwidth : primeBits.length = Nat.log 2 p + 1) :
    (initializeSelected p D primeBits hvalue hwidth).ring =
      initializedRing p D primeBits hvalue hwidth (selectedCoefficientCode p D)
        (QuarticSearch.liftedCoefficients p (D + 1)) selectedCoefficientCode_decode := rfl

end SubexponentialSAT.SubexpSelectedConversions

end OAI.Algorithms
