import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramContext

namespace OAI.Algorithms

/-! Native literal loading and padding for coefficient-array postfix source. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg LoadImplementsGlobal)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

theorem update_run {l : ℕ} (service : Program 16 256 l) (K : ℕ)
    (v p op : Bool) (code depth old new : List Bool) (context : Fin 252 → List Bool)
    (h : RunsIn service K
      ((⟨(physicalCfg (some service.entry) v p op code depth old context).regs,
        operandStore context code depth old⟩ : State 16 256).withPC (some service.entry))
      ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
        State 16 256).withPC none)) :
    RunsIn service K (physicalCfg (some service.entry) v p op code depth old context)
      (physicalCfg none false false false code depth new context) := by
  have he : ((⟨fun _ => false, Function.update (operandStore context code depth old) 27 new⟩ :
      State 16 256).withPC none) = physicalCfg none false false false code depth new context :=
    SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_after (some service.entry) v p op
      code depth old new context
  rw [he] at h
  exact h

variable (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)

include H in
theorem load_implements
    (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false) :
    LoadImplementsGlobal DensePolynomialProgram.encode (loadValue ops J)
      SubexpDenseLiteralPadding.program (loadBound (baseWidth p t) d J) context := by
  intro P xs code depth op
  let operands := Encoding.encodeList DensePolynomialProgram.encode (P :: xs)
  let tail := Encoding.encodeList DensePolynomialProgram.encode xs
  let s := operandStore context code depth operands
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore context i :=
    operandStore_frame context code depth operands i h26 h28 h27
  have hshape : s 242 = List.replicate (J*(d*baseWidth p t)) false := by
    rw [hs 242 (by decide) (by decide) (by decide),H.loaderShape]
    simp [DensePolynomialProgram.encode,hzero,List.flatten_replicate_replicate]
  have hpad : ModularArithmetic.padTo (s 242) (DensePolynomialProgram.encode P) =
      DensePolynomialProgram.encode (loadValue ops J P) := by
    rw [hshape]
    exact SubexpDensePaddingSpec.padTo_encoded RingProgram.flat ops.zeroRun.1 J
      (d*baseWidth p t) P hzero (fun x _ => RingProgram.flat_length x)
  apply update_run _ _ true false op code depth operands
    (Encoding.encodeList DensePolynomialProgram.encode (loadValue ops J P :: xs)) context
  have h := SubexpDenseLiteralPadding.program_runsIn s
    (physicalCfg (some SubexpDenseLiteralPadding.program.entry) true false op code depth operands context).regs
    (DensePolynomialProgram.encode P) tail rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact H.empty21)
    (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 99 (by decide) (by decide) (by decide)]; exact H.empty99)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact H.arithmetic.scratch)
  rw [hpad] at h
  change RunsIn SubexpDenseLiteralPadding.program
    (12 * (DensePolynomialProgram.encode P).length + 16 * (s 242).length + 46) _ _ at h
  rw [hshape] at h
  simpa [hshape, loadBound, s, operands, tail, Encoding.encodeList] using h


end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
