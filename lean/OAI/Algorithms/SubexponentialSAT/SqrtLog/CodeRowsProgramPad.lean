import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-! Appending fixed-width slot words does not require pre-normalized arithmetic
outputs. The physical padding loop drops high zeros and the caller clears any
unconsumed suffix, with both costs explicit. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularPrograms

theorem padTo_value_of_lt (shape xs : List Bool) (h : BinaryArithmetic.toNat xs < 2^shape.length) :
    BinaryArithmetic.toNat (padTo shape xs)=BinaryArithmetic.toNat xs := by
  induction shape generalizing xs with
  | nil => simp only [List.length_nil,pow_zero] at h; simp [padTo]; omega
  | cons a shape ih =>
    cases xs with
    | nil =>
      simp only [padTo,toNat_cons,bitVal_false,zero_add,toNat_nil]
      have hz := ih [] (by simp)
      simpa using hz
    | cons b xs =>
      have hx : BinaryArithmetic.toNat xs < 2^shape.length := by
        simp only [toNat_cons,List.length_cons,pow_succ] at h
        omega
      simp only [padTo,toNat_cons,ih xs hx]

theorem padTo_fixedBits (shape xs : List Bool) (h : BinaryArithmetic.toNat xs < 2^shape.length) :
    padTo shape xs=SubexpLiftRing.fixedBits shape.length (BinaryArithmetic.toNat xs) := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp [padTo_length]
  · rw [padTo_value_of_lt shape xs h,SubexpLiftRing.toNat_fixedBits_of_lt _ _ h]

theorem appendWord_trace (regs : Fin 8 → Bool) (shape xs acc : List Bool)
    (h : BinaryArithmetic.toNat xs < 2^shape.length) :
    ∃ rf, Trace paddingProgram (4*shape.length+3)
      (paddingCfg (some 0) regs shape xs acc)
      (paddingCfg none rf [] (xs.drop shape.length)
        ((SubexpLiftRing.fixedBits shape.length (BinaryArithmetic.toNat xs)).reverse++acc)) := by
  obtain ⟨rf,ht⟩ := SubexpDenseLiteralPadding.padding_trace_any regs shape xs acc
  exact ⟨rf,by simpa only [padTo_fixedBits shape xs h] using ht⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
