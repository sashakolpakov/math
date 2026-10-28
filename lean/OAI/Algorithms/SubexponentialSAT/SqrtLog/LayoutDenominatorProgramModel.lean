import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgramCached

namespace OAI.Algorithms

/-! The concrete extension-ring denominator program. It first lifts the actual
scalar-half word, then runs the paid native multiplication loop. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram

def command : Code :=
  .seq modelSignedCommand (powerCommand HornerProgram.Services.multiply)

def program := compiled command 239 252

def value (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (zero one minusOne : ModelCode t d) (half : List Bool) (R : ℕ) : ModelCode t d :=
  let ops := RingProgram.modelProgram t a M cache
  powerValue (fun x y => (ops.mulRun x y).1)
    (cachedSignedValue t a M cache zero one minusOne half []) one R

def budget (R t d : ℕ) : ℕ :=
  modelSignedBudget (baseWidth 3 t) t d +
    powerBudget R (HornerProgram.Services.mulBudget (baseWidth 3 t) d) (d*baseWidth 3 t)

theorem command_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne : ModelCode t d)
    (s : Store) (h : CachedReady t a M cache zero one minusOne s)
    (u : RingProgram.ScalarCode 3 t) (hu : s 253 = u.val)
    (h254 : s 254 = []) (h252 : s 252 = []) :
    ExecutesIn command (budget (s 239).length t d) s
      (Function.update s 252 (RingProgram.flat (value t a M cache zero one minusOne u.val (s 239).length))) := by
  let x := cachedSignedValue t a M cache zero one minusOne u.val []
  let s1 := Function.update s 255 (RingProgram.flat x)
  have h1 : ExecutesIn modelSignedCommand (modelSignedBudget (baseWidth 3 t) t d) s s1 := by
    simpa only [hu,h254,List.length_nil,Nat.add_zero,u.property] using
      cachedSignedCommand_run t a M cache hz zero one minusOne s h
  have h2 := powerCommand_run s RingProgram.flat HornerProgram.Services.multiply
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d) (d*baseWidth 3 t)
    (HornerProgram.Services.multiply_spec 3 t M cache hz (modelTable t a M cache) s h.native)
    (fun x => (RingProgram.flat_length x).le) s1 x
    one
    (CRTLocalProgram.lowFrame_update (CRTLocalProgram.lowFrame_refl s) 255 (by decide) _)
    (by simp [s1]) (by simpa [s1] using h.one)
    (by simpa [s1] using h.clean.1) (by simpa [s1] using h.clean.2.1)
    (by simpa [s1] using h.clean.2.2.1) (by simpa [s1] using h.clean.2.2.2.1)
    (by simpa [s1] using h.clean.2.2.2.2) (by simpa [s1] using h.bits)
    (by simpa [s1] using h252)
  have he : Function.update (Function.update s1 255 []) 252
      (RingProgram.flat (powerValue
        (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
        x one (s1 239).length)) =
      Function.update s 252 (RingProgram.flat (value t a M cache zero one minusOne u.val (s 239).length)) := by
    simp [s1,value,x,← h.output]
  rw [he] at h2
  simpa only [command,budget,s1,Function.update_of_ne (show (239:Fin 256)≠255 by decide)]
    using h1.seq h2

theorem ready_after {t d : ℕ} {a : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {zero one minusOne : ModelCode t d} {s : Store}
    (h : CachedReady t a M cache zero one minusOne s) (out : ModelCode t d) :
    CachedReady t a M cache zero one minusOne
      (Function.update s 252 (RingProgram.flat out)) := by
  refine ⟨h.native.frame (CRTLocalProgram.lowFrame_update
    (CRTLocalProgram.lowFrame_refl s) 252 (by decide) _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Clean] using h.clean
  · simpa using h.zero
  · simpa using h.one
  · simpa using h.minusOne
  · simpa using h.bits
  · simpa using h.accumulator
  · simpa using h.place
  · simpa using h.output

theorem value_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (zero one minusOne : ModelCode t d)
    (hz : (RingProgram.modelRing t ht hd a M cache).decode zero=0)
    (ho : (RingProgram.modelRing t ht hd a M cache).decode one=1)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (half : List Bool) (R : ℕ) :
    (RingProgram.modelRing t ht hd a M cache).decode (value t a M cache zero one minusOne half R) =
      (BinaryArithmetic.toNat half : a.O t)^(R-1) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  have he := CRTLocalProgram.iterate_mul_decode ops.decode
    (fun x y => (ops.mulRun x y).1) ops.mul_correct
    (cachedSignedValue t a M cache zero one minusOne half []) one (R-1)
  have hx : ops.decode (cachedSignedValue t a M cache zero one minusOne half []) =
      (BinaryArithmetic.toNat half : a.O t) := by
    have hx := signedValue_decode ops.decode (fun x y => (ops.mulRun x y).1)
      (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct
      zero one minusOne hz ho hm half []
    change ops.decode (signedValue (fun x y => (ops.mulRun x y).1)
      (fun x y => (ops.addRun x y).1) zero one minusOne half []) = _
    simpa using hx
  rw [ho,one_mul,hx] at he
  exact he

theorem value_inverse (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (zero one minusOne : ModelCode t d)
    (hz : (RingProgram.modelRing t ht hd a M cache).decode zero=0)
    (ho : (RingProgram.modelRing t ht hd a M cache).decode one=1)
    (hm : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (u : RingProgram.ScalarCode 3 t)
    (hu : (2:ZMod (3^t))*wordValue 3 t u=1) (R : ℕ) :
    (RingProgram.modelRing t ht hd a M cache).decode (value t a M cache zero one minusOne u.val R) *
      (2:a.O t)^(R-1)=1 := by
  have hh : (BinaryArithmetic.toNat u.val : a.O t)*(2:a.O t)=1 := by
    have hm := congrArg (LiftRing.of (a.F t)) hu
    simpa [wordValue, map_mul, map_one, map_ofNat, mul_comm] using hm
  rw [value_decode t ht hd a M cache zero one minusOne hz ho hm u.val R,← mul_pow,hh,one_pow]

def polynomialBudget (R B d : ℕ) : ℕ :=
  B*(100000*(d+1)^3*(B+1)^2+80*d*B+110) +
    200000*(d+1)^3*(B+1)^2+203*d*B+251 +
    R*(50000*(d+1)^3*(B+1)^2+8*d*B+11)+7*R+27*d*B+32

theorem budget_polynomial (R t d : ℕ) :
    budget R t d ≤ polynomialBudget R (baseWidth 3 t) d := by
  have hs := (modelSignedBudget_le_scaled (baseWidth 3 t) t d).trans
    (modelScaledBudget_polynomial (baseWidth 3 t) t d)
  have hm := HornerProgram.Services.mulBudget_polynomial (baseWidth 3 t) d
  unfold budget powerBudget polynomialBudget
  have hp := Nat.mul_le_mul (Nat.sub_le R 1)
    (Nat.add_le_add_right (Nat.add_le_add_right hm (8*(d*baseWidth 3 t))) 11)
  simp only [Nat.mul_assoc] at hs hp ⊢
  omega

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
