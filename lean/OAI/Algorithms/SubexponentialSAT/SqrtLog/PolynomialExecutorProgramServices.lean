import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramLoad
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramFixed

namespace OAI.Algorithms

/-! Concrete native add, truncated multiply and padding services for the
source-row postfix interpreter on arbitrary-degree coefficient arrays. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg ImplementsOnGlobal LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore preparedStore operandStore_frame preparedStore_frame)

def addProgram := SubexpRowPostfixServices.program DensePolynomialProgram.AddService.command
def mulProgram := SubexpRowPostfixServices.program DensePolynomialProgram.Fixed.mulCommand

variable (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)

include H in
theorem add_implements (hB : 0 < baseWidth p t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1) :
    ImplementsOnGlobal (fun P : List (Coeff (baseWidth p t) d) => P.length = J)
      DensePolynomialProgram.encode (addValue ops) false addProgram
      (fun _ _ => binaryBound (DensePolynomialProgram.AddService.budget d (baseWidth p t) J J)
        (J*(d*baseWidth p t))) context := by
  intro P Q hP hQ xs code depth
  let operands := Encoding.encodeList DensePolynomialProgram.encode (Q :: P :: xs)
  let tail := Encoding.encodeList DensePolynomialProgram.encode xs
  let s := operandStore context code depth operands
  let sp := preparedStore context code depth operands
    (DensePolynomialProgram.encode P) (DensePolynomialProgram.encode Q) tail
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore context i :=
    operandStore_frame context code depth operands i h26 h28 h27
  have harith := DensePolynomialProgram.Fixed.add_spec p t M cache ops table hB hadd sp J width frame
    (H.prepared_arithmetic code depth operands _ _ tail)
  have hr := harith sp ⟨P,hP⟩ ⟨Q,hQ⟩ (CRTLocalProgram.lowFrame_refl sp)
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,DensePolynomialProgram.Fixed.encode])
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,DensePolynomialProgram.Fixed.encode])
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,operandStore_frame,
      H.empty244])
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,operandStore_frame,
      H.empty245])
  apply update_run _ _ true true false code depth operands
    (Encoding.encodeList DensePolynomialProgram.encode (addValue ops P Q :: xs)) context
  have h := SubexpRowPostfixServices.program_runsIn DensePolynomialProgram.AddService.command
    (DensePolynomialProgram.AddService.budget d (baseWidth p t) J J) s
    (physicalCfg (some addProgram.entry) true true false code depth operands context).regs
    (DensePolynomialProgram.encode P) (DensePolynomialProgram.encode Q) tail
    (DensePolynomialProgram.encode (addValue ops P Q)) rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.arithmetic.scratch)
    (by rw [hs 240 (by decide) (by decide) (by decide)]; exact H.empty240)
    (by rw [hs 241 (by decide) (by decide) (by decide)]; exact H.empty241)
    (by rw [hs 244 (by decide) (by decide) (by decide)]; exact H.empty244) hr
  have hlen : (addValue ops P Q).length = J := by
    unfold addValue
    rw [SubexpPolynomialAddService.addProgram_length,hP,hQ,Nat.max_self]
  simpa [addProgram,binaryBound,DensePolynomialProgram.encode_length,hP,hQ,hlen,
    s, operands, tail, Encoding.encodeList] using h

include H in
theorem mul_implements (hB : 0 < baseWidth p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1) :
    ImplementsOnGlobal (fun P : List (Coeff (baseWidth p t) d) => P.length = J)
      DensePolynomialProgram.encode (mulValue ops J) true mulProgram
      (fun _ _ => binaryBound (DensePolynomialProgram.nativeMulBudget J d (baseWidth p t))
        (J*(d*baseWidth p t))) context := by
  intro P Q hP hQ xs code depth
  let operands := Encoding.encodeList DensePolynomialProgram.encode (Q :: P :: xs)
  let tail := Encoding.encodeList DensePolynomialProgram.encode xs
  let s := operandStore context code depth operands
  let sp := preparedStore context code depth operands
    (DensePolynomialProgram.encode P) (DensePolynomialProgram.encode Q) tail
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore context i :=
    operandStore_frame context code depth operands i h26 h28 h27
  have hp (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27)
      (h240 : i ≠ 240) (h241 : i ≠ 241) :
      sp i = SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore context i :=
    preparedStore_frame context code depth operands _ _ tail i h26 h28 h27 h240 h241
  have harith := DensePolynomialProgram.Fixed.mul_spec p t M cache ops table hB hz hadd hmul sp J width frame
    (H.prepared_arithmetic code depth operands _ _ tail)
    (H.prepared_buffers code depth operands _ _ tail)
    (by rw [hp 121 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H.empty121)
    (by rw [hp 122 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H.empty122)
    (by rw [hp 192 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H.zeroArray)
    (by rw [hp 193 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H.dimension)
  have hr := harith sp ⟨P,hP⟩ ⟨Q,hQ⟩ (CRTLocalProgram.lowFrame_refl sp)
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,DensePolynomialProgram.Fixed.encode])
    (by simp [sp,preparedStore,SubexpRowPostfixServices.prepared,DensePolynomialProgram.Fixed.encode])
    (by rw [hp 244 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H.empty244)
    (by rw [hp 245 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact H.empty245)
  apply update_run _ _ true true true code depth operands
    (Encoding.encodeList DensePolynomialProgram.encode (mulValue ops J P Q :: xs)) context
  have h := SubexpRowPostfixServices.program_runsIn DensePolynomialProgram.Fixed.mulCommand
    (DensePolynomialProgram.nativeMulBudget J d (baseWidth p t)) s
    (physicalCfg (some mulProgram.entry) true true true code depth operands context).regs
    (DensePolynomialProgram.encode P) (DensePolynomialProgram.encode Q) tail
    (DensePolynomialProgram.encode (mulValue ops J P Q)) rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.arithmetic.scratch)
    (by rw [hs 240 (by decide) (by decide) (by decide)]; exact H.empty240)
    (by rw [hs 241 (by decide) (by decide) (by decide)]; exact H.empty241)
    (by rw [hs 244 (by decide) (by decide) (by decide)]; exact H.empty244) hr
  simpa [mulProgram,binaryBound,DensePolynomialProgram.encode_length,hP,hQ,
    mulValue,DensePolynomialProgram.result_length,s,operands,tail,
    Encoding.encodeList] using h


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
