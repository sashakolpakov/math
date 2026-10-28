import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgramScale
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel

namespace OAI.Algorithms

/-! Concrete, fixed native programs lifting a pair of arbitrary little-endian
binary words to the actual RingModel. There is no integer-lifting callback.
The only runtime constants are explicit represented ring caches. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

abbrev ModelCode (t d : ℕ) := RingProgram.Code (RingProgram.ScalarCode 3 t) d

def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) :=
  (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

def modelMinusOne (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  (ops.negRun ops.oneRun.1).1

structure ModelReady (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (s : Store) : Prop where
  native : HornerProgram.Services.NativeReady 3 t M cache (modelTable t a M cache) s
  clean : Clean s
  zero : s 249 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1
  one : s 250 = RingProgram.flat (RingProgram.modelProgram t a M cache).oneRun.1
  minusOne : s 251 = RingProgram.flat (modelMinusOne t a M cache)
  bits : s 246 = []
  accumulator : s 247 = []
  place : s 248 = []
  output : s 255 = []

def modelSignedCommand : Code := signedCommand HornerProgram.Services.multiply HornerProgram.Services.add
def modelScaledCommand : Code := scaledCommand HornerProgram.Services.multiply HornerProgram.Services.add
def modelSignedMachine := compiled modelSignedCommand 253 255
def modelScaledMachine := compiled modelScaledCommand 253 255

def modelSignedValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (positive negative : List Bool) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  signedValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    ops.zeroRun.1 ops.oneRun.1 (modelMinusOne t a M cache) positive negative

def modelScaledValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (invDenom : ModelCode t d) (positive negative : List Bool) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  scaledValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1)
    ops.zeroRun.1 ops.oneRun.1 (modelMinusOne t a M cache) invDenom positive negative

def modelSignedBudget (bits t d : ℕ) : ℕ :=
  signedBudget bits (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
def modelScaledBudget (bits t d : ℕ) : ℕ :=
  scaledBudget bits (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)

theorem modelMinusOne_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (RingProgram.modelRing t ht hd a M cache).decode (modelMinusOne t a M cache) = -1 := by
  let ops := RingProgram.modelRing t ht hd a M cache
  change ops.decode (ops.negRun ops.oneRun.1).1 = -1
  rw [ops.neg_correct, ops.one_correct]

theorem modelSignedValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (positive negative : List Bool) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (modelSignedValue t a M cache positive negative) =
      (((BinaryArithmetic.toNat positive : ℤ) - (BinaryArithmetic.toNat negative : ℤ) : ℤ) : a.O t) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  exact signedValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
    (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
    ops.zeroRun.1 ops.oneRun.1 (modelMinusOne t a M cache) ops.zero_correct ops.one_correct
    (modelMinusOne_decode t ht hd a M cache) positive negative

theorem modelScaledValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (invDenom : ModelCode t d) (positive negative : List Bool) :
    (RingProgram.modelRing t ht hd a M cache).decode
      (modelScaledValue t a M cache invDenom positive negative) =
      -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        (((BinaryArithmetic.toNat positive : ℤ) - (BinaryArithmetic.toNat negative : ℤ) : ℤ) : a.O t) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  exact scaledValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
    (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
    ops.zeroRun.1 ops.oneRun.1 (modelMinusOne t a M cache) invDenom ops.zero_correct ops.one_correct
    (modelMinusOne_decode t ht hd a M cache) positive negative

theorem modelSignedCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (h : ModelReady t a M cache s) :
    ExecutesIn modelSignedCommand (modelSignedBudget ((s 253).length + (s 254).length) t d) s
      (Function.update s 255 (RingProgram.flat (modelSignedValue t a M cache (s 253) (s 254)))) := by
  exact signedCommand_run s RingProgram.flat HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (HornerProgram.Services.add_spec 3 t M cache (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s
    (RingProgram.modelProgram t a M cache).zeroRun.1 (RingProgram.modelProgram t a M cache).oneRun.1
    (modelMinusOne t a M cache) (lowFrame_refl s) h.clean h.zero h.one h.minusOne
    h.bits h.accumulator h.place h.output

theorem modelScaledCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (h : ModelReady t a M cache s)
    (invDenom : ModelCode t d) (hi : s 252 = RingProgram.flat invDenom) :
    ExecutesIn modelScaledCommand (modelScaledBudget ((s 253).length + (s 254).length) t d) s
      (Function.update s 255 (RingProgram.flat (modelScaledValue t a M cache invDenom (s 253) (s 254)))) := by
  exact scaledCommand_run s RingProgram.flat HornerProgram.Services.multiply HornerProgram.Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d) (d * baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (HornerProgram.Services.add_spec 3 t M cache (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s
    (RingProgram.modelProgram t a M cache).zeroRun.1 (RingProgram.modelProgram t a M cache).oneRun.1
    (modelMinusOne t a M cache) invDenom (lowFrame_refl s) h.clean h.zero h.one h.minusOne hi
    h.bits h.accumulator h.place h.output

theorem modelSignedMachine_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (h : ModelReady t a M cache s) (regs : Fin 16 → Bool) :
    ∃ (out : ModelCode t d) (rf : Fin 16 → Bool),
      RunsIn modelSignedMachine (modelSignedBudget ((s 253).length + (s 254).length) t d + 1)
        ((⟨regs, s⟩ : Data).withPC (some modelSignedMachine.entry))
        ((⟨rf, Function.update s 255 (RingProgram.flat out)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        (((BinaryArithmetic.toNat (s 253) : ℤ) - (BinaryArithmetic.toNat (s 254) : ℤ) : ℤ) : a.O t) := by
  obtain ⟨n, rf, hn, he⟩ := modelSignedCommand_run t a M cache hz s h regs
  refine ⟨modelSignedValue t a M cache (s 253) (s 254), rf, ?_,
    modelSignedValue_decode t ht hd a M cache (s 253) (s 254)⟩
  exact ⟨n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 253 255⟩

theorem modelScaledMachine_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (h : ModelReady t a M cache s) (invDenom : ModelCode t d)
    (hi : s 252 = RingProgram.flat invDenom) (regs : Fin 16 → Bool) :
    ∃ (out : ModelCode t d) (rf : Fin 16 → Bool),
      RunsIn modelScaledMachine (modelScaledBudget ((s 253).length + (s 254).length) t d + 1)
        ((⟨regs, s⟩ : Data).withPC (some modelScaledMachine.entry))
        ((⟨rf, Function.update s 255 (RingProgram.flat out)⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        -((RingProgram.modelRing t ht hd a M cache).decode invDenom) *
        (((BinaryArithmetic.toNat (s 253) : ℤ) - (BinaryArithmetic.toNat (s 254) : ℤ) : ℤ) : a.O t) := by
  obtain ⟨n, rf, hn, he⟩ := modelScaledCommand_run t a M cache hz s h invDenom hi regs
  refine ⟨modelScaledValue t a M cache invDenom (s 253) (s 254), rf, ?_,
    modelScaledValue_decode t ht hd a M cache invDenom (s 253) (s 254)⟩
  exact ⟨n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 253 255⟩

/-- Explicit polynomial bound in input bit length, extension degree and scalar
word width. No dependence on the integers' magnitudes occurs. -/
theorem modelScaledBudget_polynomial (bits t d : ℕ) :
    modelScaledBudget bits t d ≤
      bits * (100000*(d+1)^3*(baseWidth 3 t+1)^2 + 80*d*baseWidth 3 t + 110) +
        200000*(d+1)^3*(baseWidth 3 t+1)^2 + 203*d*baseWidth 3 t + 251 := by
  have hm := HornerProgram.Services.mulBudget_polynomial (baseWidth 3 t) d
  have ha := HornerProgram.Services.addBudget_polynomial (baseWidth 3 t) d
  have hs := Nat.mul_le_mul_left bits (Nat.mul_le_mul_left 2 ha)
  unfold modelScaledBudget scaledBudget signedBudget
  ring_nf at *
  omega

theorem modelSignedBudget_le_scaled (bits t d : ℕ) :
    modelSignedBudget bits t d ≤ modelScaledBudget bits t d := by
  unfold modelSignedBudget modelScaledBudget scaledBudget
  omega

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
