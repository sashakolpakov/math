import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramHorner
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCorrectionAlgebra

namespace OAI.Algorithms

/-! The jet loop runs J times independently of the scalar precision t. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open Polynomial
open scoped BigOperators
open SubexponentialSAT.SubexpTruncatedGeometric

 theorem truncatedHorner_denote {S R : Type*} [CommRing R]
    (J : ℕ) (zero one z : S) (mulOp addOp : S → S → S) (denote : S → R[X])
    (Z : R[X]) (hzero : denote zero = 0) (hone : denote one = Truncation.trunc J 1)
    (hz : denote z = Truncation.trunc J Z)
    (ha : ∀ a b, denote (addOp a b) = denote a + denote b)
    (hm : ∀ a b, denote (mulOp a b) = Truncation.trunc J (denote a * denote b)) (n : ℕ) :
    denote ((hornerValue mulOp addOp z one)^[n] zero) =
      Truncation.trunc J (∑ i ∈ Finset.range n, Z^i) := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [hornerValue, ha, hm, ih, hz, hone, trunc_mul_trunc,
        ← Truncation.trunc_add]
      congr 1
      simpa only [mul_comm] using (@geom_sum_succ R[X] _ Z n).symm

def correctionValue {S : Type*} (mulOp addOp : S → S → S)
    (zero one negInverse inverse factor jet : S) (J : ℕ) : S :=
  let z := addOp (mulOp factor negInverse) one
  let series := (hornerValue mulOp addOp z one)^[J] zero
  mulOp (mulOp series inverse) jet

theorem correctionValue_denote {S R : Type*} [CommRing R]
    (J : ℕ) (zero one negInverse inverse factor jet : S)
    (mulOp addOp : S → S → S) (denote : S → R[X]) (P Jet : R[X]) (a : R)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc J 1)
    (hneg : denote negInverse = Truncation.trunc J (C (-a)))
    (hinv : denote inverse = Truncation.trunc J (C a))
    (hfactor : denote factor = Truncation.trunc J P) (hjet : denote jet = Jet)
    (ha : ∀ x y, denote (addOp x y) = denote x + denote y)
    (hm : ∀ x y, denote (mulOp x y) = Truncation.trunc J (denote x * denote y)) :
    denote (correctionValue mulOp addOp zero one negInverse inverse factor jet J) =
      TruncatedInverse.correctedJet P Jet a J := by
  let z := addOp (mulOp factor negInverse) one
  have hz : denote z = Truncation.trunc J (1 - C a * P) := by
    dsimp [z]
    rw [ha, hm, hfactor, hneg, trunc_mul_trunc, hone, ← Truncation.trunc_add]
    congr 1
    simp only [map_neg]
    ring
  have hs := truncatedHorner_denote J zero one z mulOp addOp denote _ hzero hone hz ha hm J
  change denote (mulOp (mulOp ((hornerValue mulOp addOp z one)^[J] zero) inverse) jet) = _
  rw [hm, hm, hs, hinv, trunc_mul_trunc, hjet]
  simp only [TruncatedInverse.correctedJet, TruncatedInverse.inverse]
  congr 1
  rw [mul_comm]
  congr 1
  rw [mul_comm]
  rfl

theorem truncatedPower_denote {S R : Type*} [CommRing R]
    (J : ℕ) (denote : S → R[X]) (mulOp : S → S → S)
    (hm : ∀ a b, denote (mulOp a b) = Truncation.trunc J (denote a * denote b))
    (factor seed : S) (F P : R[X])
    (hf : denote factor = Truncation.trunc J F)
    (hs : denote seed = Truncation.trunc J P) (n : ℕ) :
    denote ((fun a => mulOp a factor)^[n] seed) = Truncation.trunc J (P * F^n) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
      rw [Function.iterate_succ_apply', hm, ih, hf, trunc_mul_trunc]
      simp only [pow_succ, mul_assoc]

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
