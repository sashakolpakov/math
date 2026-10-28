import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgramPrimitive

namespace OAI.Algorithms

/-! Cache-extensional interface for the same fixed integer-lift programs.
Setup may supply any represented zero, one and minus-one bytes whose decoded
values are correct. This avoids requiring its constant-vector construction
to equal a particular arithmetic expression byte for byte. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

structure CachedReady (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (s : Store) : Prop where
  native : HornerProgram.Services.NativeReady 3 t M cache (modelTable t a M cache) s
  clean : Clean s
  zero : s 249 = RingProgram.flat zero
  one : s 250 = RingProgram.flat one
  minusOne : s 251 = RingProgram.flat minusOne
  bits : s 246 = []
  accumulator : s 247 = []
  place : s 248 = []
  output : s 255 = []

def cachedSignedValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (positive negative : List Bool) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  signedValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    zero one minusOne positive negative

def cachedScaledValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne invDenom : ModelCode t d) (positive negative : List Bool) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  scaledValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    zero one minusOne invDenom positive negative

theorem cachedSignedCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne : ModelCode t d) (s : Store) (h : CachedReady t a M cache zero one minusOne s) :
    ExecutesIn modelSignedCommand (modelSignedBudget ((s 253).length + (s 254).length) t d) s
      (Function.update s 255 (RingProgram.flat
        (cachedSignedValue t a M cache zero one minusOne (s 253) (s 254)))) := by
  exact signedCommand_run s RingProgram.flat HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (HornerProgram.Services.add_spec 3 t M cache (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s zero one minusOne (lowFrame_refl s)
    h.clean h.zero h.one h.minusOne h.bits h.accumulator h.place h.output

theorem cachedScaledCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d) (s : Store)
    (h : CachedReady t a M cache zero one minusOne s) (hi : s 252 = RingProgram.flat invDenom) :
    ExecutesIn modelScaledCommand (modelScaledBudget ((s 253).length + (s 254).length) t d) s
      (Function.update s 255 (RingProgram.flat
        (cachedScaledValue t a M cache zero one minusOne invDenom (s 253) (s 254)))) := by
  exact scaledCommand_run s RingProgram.flat HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (HornerProgram.Services.add_spec 3 t M cache (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s zero one minusOne invDenom (lowFrame_refl s)
    h.clean h.zero h.one h.minusOne hi h.bits h.accumulator h.place h.output

theorem cachedSignedMachine_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (s : Store) (h : CachedReady t a M cache zero one minusOne s) (regs : Fin 16 → Bool) :
    ∃ (out : ModelCode t d) (rf : Fin 16 → Bool),
      RunsIn modelSignedMachine (modelSignedBudget ((s 253).length + (s 254).length) t d + 1)
        ((⟨regs, s⟩ : Data).withPC (some modelSignedMachine.entry))
        ((⟨rf, Function.update s 255 (RingProgram.flat out)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        (((BinaryArithmetic.toNat (s 253) : ℤ) - (BinaryArithmetic.toNat (s 254) : ℤ) : ℤ) : a.O t) := by
  obtain ⟨n, rf, hn, he⟩ := cachedSignedCommand_run t a M cache hz zero one minusOne s h regs
  refine ⟨cachedSignedValue t a M cache zero one minusOne (s 253) (s 254), rf,
    ⟨n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 253 255⟩, ?_⟩
  let ops := RingProgram.modelRing t ht hd a M cache
  exact signedValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
    (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
    zero one minusOne hzero hone hminus (s 253) (s 254)

theorem cachedScaledMachine_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (s : Store) (h : CachedReady t a M cache zero one minusOne s)
    (hi : s 252 = RingProgram.flat invDenom) (regs : Fin 16 → Bool) :
    ∃ (out : ModelCode t d) (rf : Fin 16 → Bool),
      RunsIn modelScaledMachine (modelScaledBudget ((s 253).length + (s 254).length) t d + 1)
        ((⟨regs, s⟩ : Data).withPC (some modelScaledMachine.entry))
        ((⟨rf, Function.update s 255 (RingProgram.flat out)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        (((BinaryArithmetic.toNat (s 253) : ℤ) - (BinaryArithmetic.toNat (s 254) : ℤ) : ℤ) : a.O t) := by
  obtain ⟨n, rf, hn, he⟩ := cachedScaledCommand_run t a M cache hz zero one minusOne invDenom s h hi regs
  refine ⟨cachedScaledValue t a M cache zero one minusOne invDenom (s 253) (s 254), rf,
    ⟨n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 253 255⟩, ?_⟩
  let ops := RingProgram.modelRing t ht hd a M cache
  exact scaledValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
    (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
    zero one minusOne invDenom hzero hone hminus (s 253) (s 254)

theorem cachedSignedMachine_primitive (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (s : Store) (h : CachedReady t a M cache zero one minusOne s) (regs : Fin 16 → Bool) :
    ∃ (out : ModelCode t d) (rf : Fin 16 → Bool),
      Computation.RunsIn (primitive modelSignedMachine).step
        (primitiveOverhead modelSignedMachine *
          (polynomialBudget ((s 253).length + (s 254).length) t d + 1))
        (primitiveCfg modelSignedMachine ((⟨regs, s⟩ : Data).withPC (some modelSignedMachine.entry)))
        (primitiveCfg modelSignedMachine
          ((⟨rf, Function.update s 255 (RingProgram.flat out)⟩ : Data).withPC none)) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        (((BinaryArithmetic.toNat (s 253) : ℤ) - (BinaryArithmetic.toNat (s 254) : ℤ) : ℤ) : a.O t) := by
  obtain ⟨out, rf, he, hv⟩ := cachedSignedMachine_correct t ht hd a M cache hz
    zero one minusOne hzero hone hminus s h regs
  refine ⟨out, rf, ?_, hv⟩
  exact (BitProgram.primitive_execution modelSignedMachine he).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      ((modelSignedBudget_le_scaled _ _ _).trans (modelScaledBudget_polynomial _ _ _)) 1))

theorem cachedScaledMachine_primitive (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (s : Store) (h : CachedReady t a M cache zero one minusOne s)
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
  obtain ⟨out, rf, he, hv⟩ := cachedScaledMachine_correct t ht hd a M cache hz
    zero one minusOne invDenom hzero hone hminus s h hi regs
  refine ⟨out, rf, ?_, hv⟩
  exact (BitProgram.primitive_execution modelScaledMachine he).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (modelScaledBudget_polynomial _ _ _) 1))

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
