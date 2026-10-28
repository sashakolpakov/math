import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramPairSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramMul
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramAddService
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramConstructorSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramZero

namespace OAI.Algorithms

/-! Fixed native dense-polynomial arithmetic with arbitrary runtime ring
coefficient width. Native ring multiplication and every convolution scan are
included in the cost, and the output has the usual polynomial meaning. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- One finite instruction table, independent of all dimensions. -/
def nativeMulCommand : Code := mulCommand Pair.command

def nativeMulProgram := compiled nativeMulCommand 240 244

def nativeMulBudget (J degree B : ℕ) : ℕ := mulBudget J (degree*B) (Pair.budget degree B J)

/-- An explicit polynomial upper bound for the fully native trace. -/
theorem nativeMulBudget_polynomial (J degree B : ℕ) :
    nativeMulBudget J degree B ≤ 100000 * (J+1)^3 * (degree+1)^3 * (B+1)^2 := by
  unfold nativeMulBudget mulBudget convolutionBudget outerCost Pair.budget
    RingCall.budget RingScan.serviceMulBudget RingTriple.expandBudget Cell.eventBudget Cell.addBudget
  ring_nf
  omega

/-- With nonempty coefficients, the bound is polynomial in the actual
serialized coefficient width W=degree*B and the runtime array length. -/
theorem nativeMulBudget_width (J degree B : ℕ) (hd : 0 < degree) (hB : 0 < B) :
    nativeMulBudget J degree B ≤ 100000 * (J+1)^3 * (degree*B+1)^5 := by
  have hdegree : degree ≤ degree*B := Nat.le_mul_of_pos_right degree hB
  have hword : B ≤ degree*B := Nat.le_mul_of_pos_left B hd
  calc
    _ ≤ 100000 * (J+1)^3 * (degree+1)^3 * (B+1)^2 := nativeMulBudget_polynomial J degree B
    _ ≤ 100000 * (J+1)^3 * (degree*B+1)^3 * (degree*B+1)^2 := by gcongr
    _ = _ := by ring

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {degree : ℕ}
  (ops : SubexponentialSAT.SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) degree))
  (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

/-- Cached multiplication, with its local native ring contract discharged. -/
theorem native_mul_eval (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (P Q : List (Coeff (baseWidth p t) degree))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h121 : s 121 = []) (h122 : s 122 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J ops.zeroRun.1))
    (hJ : (s 243).length = J) :
    ExecutesIn nativeMulCommand (nativeMulBudget J degree (baseWidth p t)-1) s
      (Function.update s 244 (encode (result ops J P Q))) :=
  mul_service_eval Pair.command s ops J (Pair.budget degree (baseWidth p t) J) P Q
    (PairSpec.pairSpec p t M cache ops table hB hz hadd hmul s scalarWidth frame H J)
    H.width hempty H.scratch h121 h122 h244 h245 hP hQ hleft hright hzero hJ

theorem native_mul_trace (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (s : Store) (J : ℕ) (P Q : List (Coeff (baseWidth p t) degree))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady p t M cache table s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h121 : s 121 = []) (h122 : s 122 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J ops.zeroRun.1))
    (hJ : (s 243).length = J) (regs : Fin 16 → Bool) :
    ∃ n ≤ nativeMulBudget J degree (baseWidth p t), ∃ regs',
      Trace nativeMulProgram n
        ((⟨regs,s⟩ : Data).withPC (some nativeMulProgram.entry))
        ((⟨regs',Function.update s 244 (encode (result ops J P Q))⟩ : Data).withPC none) :=
  mul_service_trace Pair.command s ops J (Pair.budget degree (baseWidth p t) J) P Q
    (PairSpec.pairSpec p t M cache ops table hB hz hadd hmul s scalarWidth frame H J)
    H.width hempty H.scratch h121 h122 h244 h245 hP hQ hleft hright hzero hJ regs

/-- The cached multiplication table belonging to the supplied ternary model. -/
def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) :=
  (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

@[simp] theorem model_add_native (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (x y : Coeff (baseWidth 3 t) d) :
    ((RingProgram.modelProgram t a M cache).addRun x y).1 =
      (RingProgram.addRun (RingProgram.scalarProgram 3 t M cache) x y).1 := rfl

@[simp] theorem model_mul_native (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (x y : Coeff (baseWidth 3 t) d) :
    ((RingProgram.modelProgram t a M cache).mulRun x y).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram 3 t M cache) (modelTable t a M cache) x y).1 := rfl


/-- Complete model-ring multiplication: one fixed native trace and the exact
truncated polynomial product under the model's coefficient decoder. -/
theorem model_mul_trace (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hB : 0 < baseWidth 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (J : ℕ) (P Q : List (Coeff (baseWidth 3 t) d))
    (scalarWidth : List Bool) (frame : Fin 6 → List Bool)
    (H : PairSpec.BaseReady 3 t M cache (modelTable t a M cache) s scalarWidth frame)
    (hempty : ∀ i, s (bufferPorts i) = [])
    (h121 : s 121 = []) (h122 : s 122 = []) (h244 : s 244 = []) (h245 : s 245 = [])
    (hP : P.length = J) (hQ : Q.length = J)
    (hleft : s 240 = encode P) (hright : s 241 = encode Q)
    (hzero : s 242 = encode (List.replicate J (RingProgram.modelProgram t a M cache).zeroRun.1))
    (hJ : (s 243).length = J) (regs : Fin 16 → Bool) :
    let ops := RingProgram.modelRing t ht hd a M cache
    let output := result ops.program J P Q
    (∃ n ≤ nativeMulBudget J d (baseWidth 3 t), ∃ regs',
      Trace nativeMulProgram n
        ((⟨regs,s⟩ : Data).withPC (some nativeMulProgram.entry))
        ((⟨regs',Function.update s 244 (encode output)⟩ : Data).withPC none)) ∧
    SubexponentialSAT.PolynomialAlgorithm.denote (output.map ops.decode) =
      SubexponentialSAT.Truncation.trunc J (SubexponentialSAT.PolynomialAlgorithm.denote (P.map ops.decode) *
        SubexponentialSAT.PolynomialAlgorithm.denote (Q.map ops.decode)) := by
  constructor
  · exact native_mul_trace 3 t M cache (RingProgram.modelProgram t a M cache)
      (modelTable t a M cache) hB hz (fun _ _ => rfl) (fun _ _ => rfl)
      s J P Q scalarWidth frame H hempty h121 h122 h244 h245 hP hQ hleft hright hzero hJ regs
  · exact result_correct (RingProgram.modelRing t ht hd a M cache) J P Q

/-- The compiler cost is a fixed multiplicative constant for this fixed
instruction table; arbitrary tape states are allowed at both endpoints. -/
theorem native_mul_primitive {n : ℕ} {before after : Cfg 16 256 (size nativeMulCommand+1)}
    (h : Trace nativeMulProgram n before after) :
    Computation.RunsIn (primitive nativeMulProgram).step
      (primitiveOverhead nativeMulProgram * n)
      (primitiveCfg nativeMulProgram before) (primitiveCfg nativeMulProgram after) :=
  BitProgram.primitive_execution nativeMulProgram ⟨n,le_rfl,h⟩

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
