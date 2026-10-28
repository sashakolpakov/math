import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawRow
import OAI.Algorithms.SubexponentialSAT.SubexpNodeLiftData
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionScalarCanonical

namespace OAI.Algorithms

/-!
# Decode the correction scalar already emitted by the row producer

The correction program emits one canonical prime-field word followed by
three zero words. This file identifies that existing payload under the raw
row decoder. Other cache payloads may retain arbitrary representatives.
No new execution or runtime bound is asserted here.
-/

namespace SubexponentialSAT.Subexp.UniversalRowScalarDecode

open SubexpLiftRing SubexpQuarticRing SubexpSelectedConversions

private theorem flatEncode_eq_nodeEncode {B : ℕ} (a : Quad (Word B)) :
    SubexpFlatAdd.encode a = SubexpNodeLiftData.encode a := by
  simp [SubexpFlatAdd.encode, SubexpFlatAdd.quadWords, SubexpFlatAdd.flatten,
    SubexpNodeLiftData.encode, List.append_assoc]

/-- Splitting an existing fixed-width coefficient recovers all four words. -/
theorem ofBits_encode {B : ℕ} (hB : 0 < B) (a : Quad (Word B)) :
    SubexpRawQuartic.ofBits B (SubexpFlatAdd.encode a) = a := by
  apply SubexpNodeLiftData.encode_injective hB
  have h := SubexpRawQuartic.encode_ofBits B (SubexpFlatAdd.encode a)
    (SubexpFlatAdd.encode_length a)
  simpa only [flatEncode_eq_nodeEncode] using h

variable (p : ℕ) [Fact p.Prime]

/-- The same constant coefficient as the physical scalar marshaler. -/
def constantCode (z : ZMod p) : SubexpSymbolicCost.QuarticCode p 0 :=
  ⟨⟨MatrixWordEncoding.word p z, MatrixWordEncoding.word_length p z⟩,
    SubexpPreparedQuartic.zeroWord p 1, SubexpPreparedQuartic.zeroWord p 1,
    SubexpPreparedQuartic.zeroWord p 1⟩

omit [Fact p.Prime] in
/-- The correction quartet is exactly the flat encoding of its constant code. -/
theorem quartet_eq_encode (z : ZMod p) :
    CorrectionScalarCanonical.quartet p z = SubexpFlatAdd.encode (constantCode p z) := by
  simpa only [CorrectionScalarCanonical.quartet, SubexpQuarticMarshal.marshalBits,
    MatrixWordEncoding.word_length, constantCode] using
    SubexpFlatAdd.marshalBits_eq_encode_constant p 1
      (MatrixWordEncoding.word p z) (MatrixWordEncoding.word p z)
      (MatrixWordEncoding.word_length p z) (MatrixWordEncoding.word_length p z)

variable {p} (source : Prepared p 0)

theorem scalarDecode_encode (a : SubexpSymbolicCost.QuarticCode p 0) :
    SubexpRawRow.scalarDecode source (SubexpFlatAdd.encode a) = source.residueRing.decode a := by
  unfold SubexpRawRow.scalarDecode
  rw [ofBits_encode (by simp [baseWidth])]

theorem constantCode_decode (z : ZMod p) :
    source.residueRing.decode (constantCode p z) =
      algebraMap (ZMod p) (SubexpActualRing.E p) z := by
  have hz : SubexpWordLift.sourceValue p (SubexpPreparedQuartic.zeroWord p 1) = 0 := by
    have h := congrArg (LiftRing.baseReduction p 1 (by decide))
      (SubexpPreparedQuartic.zeroWord_value p 1)
    simpa only [SubexpWordLift.sourceValue, wordValue, map_natCast, map_zero] using h
  have hm : (constantCode p z).map (SubexpWordLift.sourceValue p) =
      (⟨z, 0, 0, 0⟩ : Quad (ZMod p)) := by
    simp only [constantCode, Quad.map, hz]
    change (⟨(BinaryArithmetic.toNat (MatrixWordEncoding.word p z) : ZMod p), 0, 0, 0⟩ :
      Quad (ZMod p)) = _
    rw [MatrixWordEncoding.word_field_value]
  rw [Prepared.residueRing_decode, hm, quotientDenote_const]
  rfl

/-- The correction vector's actual scalar bytes decode to their intended
prime-field value in the selected quartic residue field. -/
theorem scalarDecode_quartet (z : ZMod p) :
    SubexpRawRow.scalarDecode source (CorrectionScalarCanonical.quartet p z) =
      algebraMap (ZMod p) (SubexpActualRing.E p) z := by
  rw [quartet_eq_encode, scalarDecode_encode, constantCode_decode]

end SubexponentialSAT.Subexp.UniversalRowScalarDecode

end OAI.Algorithms
