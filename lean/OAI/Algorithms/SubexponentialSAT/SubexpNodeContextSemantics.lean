import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeContexts
import OAI.Algorithms.SubexponentialSAT.SubexpTemplateData
import OAI.Algorithms.SubexponentialSAT.SubexpMomentSourceSize

namespace OAI.Algorithms

/-! Arithmetic validity of the contexts read from actual node masters.
The target scalar unit is the word emitted by the finite constant program.
No source-service validity predicate is assumed. -/

namespace SubexponentialSAT.SubexpNodeContextSemantics

open SubexpNodeWorkspace SubexpNodeContexts SubexpLiftRing
open SubexpSelectedConversions

variable {p D : ℕ} [Fact p.Prime]

structure Masters (masters : Store) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1))) : Prop where
  sourceModulus : masters 128 = source.modulus.bits
  sourceReduction : masters 130 = SubexpQuarticFlatMul.flat source.reduction
  sourceZero : masters 131 = SubexpQuarticFlatMul.flat source.zero
  sourceWidth : (masters 129).length = baseWidth p 1
  targetWidth : (masters 10).length = baseWidth p (D+1)
  targetModulus : masters 5 = target.modulus.bits
  targetMinusOne : masters 121 = minusOne.val
  unit : masters 124 = fixedBits (baseWidth p (D+1)) 1

theorem template_good (masters : Store) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (h : Masters masters source target minusOne) :
    SubexpTemplateData.ContextGood (templateContext masters D) source target minusOne :=
  ⟨h.sourceModulus,h.sourceReduction,h.sourceZero,h.sourceWidth,h.targetWidth,
    h.targetModulus,h.targetMinusOne,rfl,rfl⟩

theorem source_good (masters : Store) (source : Prepared p 0) (target : Prepared p D)
    (minusOne : SubexpQuarticRing.Word (baseWidth p (D+1)))
    (h : Masters masters source target minusOne) (template : List Bool) (a : Fin D → ℕ) :
    SubexpMomentSourceProgram.ContextGood
      ((sourceContext masters D template).withExponent (SubexpExponentController.momentWord a)) a := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hB : 0 < baseWidth p (D+1) := by
    unfold baseWidth
    positivity
  have hcapacity : 1 < 2 ^ baseWidth p (D+1) := Nat.one_lt_pow (by omega) (by decide)
  constructor
  · rfl
  · rfl
  · change (masters 129).length ≤ (masters 10).length
    rw [h.sourceWidth,h.targetWidth]
    unfold baseWidth
    nlinarith
  · change (masters 124).length = (masters 10).length
    rw [h.unit,fixedBits_length,h.targetWidth]
  · change (BinaryArithmetic.toNat (masters 124) : ZMod (BinaryArithmetic.toNat (masters 5))) = 1
    rw [h.unit,toNat_fixedBits_of_lt _ 1 hcapacity]
    exact Nat.cast_one
  · change (masters 5).length ≤ (masters 10).length + 1
    rw [h.targetModulus,h.targetWidth]
    exact target.modulus.length_le
  · change 0 < BinaryArithmetic.toNat (masters 5)
    rw [h.targetModulus,target.modulus.value]
    positivity
  · change BinaryArithmetic.toNat (masters 5) ≤ 2 ^ (masters 10).length
    rw [h.targetModulus,target.modulus.value,h.targetWidth]
    exact modulus_le_width p (D+1)

end SubexponentialSAT.SubexpNodeContextSemantics

end OAI.Algorithms
