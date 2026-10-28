import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgramModel

namespace OAI.Algorithms

/-! Primitive bit-machine refinement. All instruction tables are fixed,
including their simulation overhead; input integer magnitudes are never loop
bounds. The sole nonconstant scan count is the total input word length. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def polynomialBudget (bits t d : ℕ) : ℕ :=
  bits * (100000*(d+1)^3*(baseWidth 3 t+1)^2 + 80*d*baseWidth 3 t + 110) +
    200000*(d+1)^3*(baseWidth 3 t+1)^2 + 203*d*baseWidth 3 t + 251

theorem modelSignedMachine_primitive (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (h : ModelReady t a M cache s) (regs : Fin 16 → Bool) :
    ∃ (out : ModelCode t d) (rf : Fin 16 → Bool),
      Computation.RunsIn (primitive modelSignedMachine).step
        (primitiveOverhead modelSignedMachine *
          (polynomialBudget ((s 253).length + (s 254).length) t d + 1))
        (primitiveCfg modelSignedMachine ((⟨regs, s⟩ : Data).withPC (some modelSignedMachine.entry)))
        (primitiveCfg modelSignedMachine
          ((⟨rf, Function.update s 255 (RingProgram.flat out)⟩ : Data).withPC none)) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        (((BinaryArithmetic.toNat (s 253) : ℤ) - (BinaryArithmetic.toNat (s 254) : ℤ) : ℤ) : a.O t) := by
  obtain ⟨out, rf, he, hv⟩ := modelSignedMachine_correct t ht hd a M cache hz s h regs
  refine ⟨out, rf, ?_, hv⟩
  apply (BitProgram.primitive_execution modelSignedMachine he).mono
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
    ((modelSignedBudget_le_scaled _ _ _).trans (modelScaledBudget_polynomial _ _ _)) 1)

theorem modelScaledMachine_primitive (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (h : ModelReady t a M cache s) (invDenom : ModelCode t d)
    (hi : s 252 = RingProgram.flat invDenom) (regs : Fin 16 → Bool) :
    ∃ (out : ModelCode t d) (rf : Fin 16 → Bool),
      Computation.RunsIn (primitive modelScaledMachine).step
        (primitiveOverhead modelScaledMachine *
          (polynomialBudget ((s 253).length + (s 254).length) t d + 1))
        (primitiveCfg modelScaledMachine ((⟨regs, s⟩ : Data).withPC (some modelScaledMachine.entry)))
        (primitiveCfg modelScaledMachine
          ((⟨rf, Function.update s 255 (RingProgram.flat out)⟩ : Data).withPC none)) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        (((BinaryArithmetic.toNat (s 253) : ℤ) - (BinaryArithmetic.toNat (s 254) : ℤ) : ℤ) : a.O t) := by
  obtain ⟨out, rf, he, hv⟩ := modelScaledMachine_correct t ht hd a M cache hz s h invDenom hi regs
  refine ⟨out, rf, ?_, hv⟩
  apply (BitProgram.primitive_execution modelScaledMachine he).mono
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (modelScaledBudget_polynomial _ _ _) 1)

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
