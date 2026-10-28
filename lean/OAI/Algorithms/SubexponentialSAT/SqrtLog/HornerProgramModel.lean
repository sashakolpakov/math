import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramModel

namespace OAI.Algorithms

/-! Native Horner evaluation in the actual arbitrary-degree unramified
RingModel. The instruction table is independent of precision, extension
degree and polynomial length. Ring caches are explicit runtime inputs. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Actual fixed Horner command, using native arbitrary-degree arithmetic. -/
def modelCommand : Code := command Services.multiply Services.add

abbrev modelMachine : Program 16 256 (size modelCommand + 1) :=
  program Services.multiply Services.add

def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) :=
  (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

def modelValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  let ops := RingProgram.modelProgram t a M cache
  fold (stepValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1) x)
    P.reverse ops.zeroRun.1

def modelBudget (n t d : ℕ) : ℕ :=
  budget n (d * baseWidth 3 t)
    (Services.mulBudget (baseWidth 3 t) d) (Services.addBudget (baseWidth 3 t) d)

theorem modelValue_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :
    (RingProgram.modelRing t ht hd a M cache).decode (modelValue t a M cache P x) =
      (PolynomialAlgorithm.denote (P.map (RingProgram.modelRing t ht hd a M cache).decode)).eval
        ((RingProgram.modelRing t ht hd a M cache).decode x) := by
  let ops := RingProgram.modelRing t ht hd a M cache
  exact output_decode ops.decode (fun x y => (ops.mulRun x y).1)
    (fun x y => (ops.addRun x y).1) ops.mul_correct ops.add_correct P x
    ops.zeroRun.1 ops.zero_correct

/-- All arithmetic service hypotheses are discharged by the actual native
programs. Remaining assumptions describe supplied bytes and clean scratch. -/
theorem modelCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : Services.NativeReady 3 t M cache (modelTable t a M cache) base)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hP : base 246 = encodePolynomial RingProgram.flat P)
    (hx : base 247 = RingProgram.flat x)
    (hseed : base 240 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hcount : (base 248).length = P.length) (hw : (base 250).length = d * baseWidth 3 t)
    (h241 : base 241 = []) (h244 : base 244 = []) (h245 : base 245 = [])
    (h251 : base 251 = []) (h252 : base 252 = []) :
    ExecutesIn modelCommand (modelBudget P.length t d) base
      (Function.update (Function.update (Function.update base 246 [])
        240 (RingProgram.flat (modelValue t a M cache P x))) 248 []) := by
  exact command_run base RingProgram.flat Services.multiply Services.add
    (fun x y => ((RingProgram.modelProgram t a M cache).mulRun x y).1)
    (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
    (Services.mulBudget (baseWidth 3 t) d) (Services.addBudget (baseWidth 3 t) d)
    (d * baseWidth 3 t)
    (Services.multiply_spec 3 t M cache hz (modelTable t a M cache) base hready)
    (Services.add_spec 3 t M cache (modelTable t a M cache) base hready)
    RingProgram.flat_length P x (RingProgram.modelProgram t a M cache).zeroRun.1
    hP hx hseed hcount hw hready.workspace.1 h241 h244 h245 h251 h252

/-- A single fixed finite BitProgram evaluates the represented polynomial in
its actual RingModel. The output witness is produced by the executable fold. -/
theorem modelMachine_correct (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : Services.NativeReady 3 t M cache (modelTable t a M cache) base)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hP : base 246 = encodePolynomial RingProgram.flat P)
    (hx : base 247 = RingProgram.flat x)
    (hseed : base 240 = RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hcount : (base 248).length = P.length) (hw : (base 250).length = d * baseWidth 3 t)
    (h241 : base 241 = []) (h244 : base 244 = []) (h245 : base 245 = [])
    (h251 : base 251 = []) (h252 : base 252 = []) (regs : Fin 16 → Bool) :
    ∃ (out : RingProgram.Code (RingProgram.ScalarCode 3 t) d) (rf : Fin 16 → Bool),
      RunsIn modelMachine (modelBudget P.length t d + 1)
        ((⟨regs, base⟩ : Data).withPC (some modelMachine.entry))
        ((⟨rf, Function.update (Function.update (Function.update base 246 [])
          240 (RingProgram.flat out)) 248 []⟩ : Data).withPC none) ∧
      (RingProgram.modelRing t ht hd a M cache).decode out =
        (PolynomialAlgorithm.denote (P.map (RingProgram.modelRing t ht hd a M cache).decode)).eval
          ((RingProgram.modelRing t ht hd a M cache).decode x) := by
  obtain ⟨n, rf, hn, he⟩ := modelCommand_run t a M cache hz base hready P x
    hP hx hseed hcount hw h241 h244 h245 h251 h252 regs
  refine ⟨modelValue t a M cache P x, rf, ?_, modelValue_decode t ht hd a M cache P x⟩
  exact ⟨n+1, Nat.add_le_add_right hn 1, compiled_halt_trace he 246 240⟩

/-- Concrete polynomial native-step bound, before the fixed primitive-machine
simulation constant. -/
theorem modelBudget_polynomial (n t d : ℕ) :
    modelBudget n t d ≤ 200000 * (n+1) * (d+1)^3 * (baseWidth 3 t+1)^2 := by
  have hm := Services.mulBudget_polynomial (baseWidth 3 t) d
  have ha := Services.addBudget_polynomial (baseWidth 3 t) d
  have hs := Nat.mul_le_mul_left n (Nat.add_le_add hm ha)
  unfold modelBudget budget
  ring_nf at *
  omega

/-- A standard constructed zero cache meets the only extra canonicality
condition required by the vector-contraction implementation. -/
theorem prepared_zero_canonical (t : ℕ) (ht : 0 < t)
    (M : SubexpPreparedQuartic.Modulus 3 t) :
    BinaryArithmetic.toNat (RingProgram.prepareScalarCache 3 t M ht).1.zero.val < 3^t :=
  RingProgram.prepareScalarCache_zero_canonical 3 t M ht

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
