import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramFlatten

namespace OAI.Algorithms

/-! The complete native source interpreter returns an ordinary flat
coefficient array on240, ready for the perturbation producer. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

def flatCommand : Code := flattenCommand program
def flatProgram := flattenProgram program

theorem flat_run {B d : ℕ} (context : Fin 252 → List Bool)
    (source : List Bool) (out : List (Coeff B d)) (K : ℕ)
    (h21 : contextStore context 21 = []) (h120 : contextStore context 120 = [])
    (h240 : contextStore context 240 = [])
    (hrun : RunsIn program K
      (physicalCfg (some program.entry) false false false source [] [] context)
      (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
        (Encoding.encodeList DensePolynomialProgram.encode [out]) context)) :
    ∃ rf, RunsIn flatProgram (K+18*(DensePolynomialProgram.encode out).length+28)
      (physicalCfg (some flatProgram.entry) false false false source [] [] context)
      ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none) :=
  flatten_run program context source out K h21 h120 h240 hrun

/-- The actual RingModel interpreter has a plain, source-derived output array.
The runtime array length remains available in protected cache193. -/
theorem model_flat_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame context)
    (e : Algorithm.Expr (List (Coeff (baseWidth 3 t) d))) :
    ∃ (out : List (Coeff (baseWidth 3 t) d)) (rf : Fin 16 → Bool),
      RunsIn flatProgram (totalBudget J e+18*(J*(d*baseWidth 3 t))+28)
        (physicalCfg (some flatProgram.entry) false false false
          (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] [] context)
        ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none) ∧
      out.length = J ∧
      meaning (RingProgram.modelRing t ht hd a M cache) out =
        Truncation.trunc J ((e.map (meaning (RingProgram.modelRing t ht hd a M cache))).eval) := by
  obtain ⟨out,hr,hl,hv⟩ := model_run t ht hd a M cache hz J width frame context H e
  obtain ⟨rf,hf⟩ := flat_run context _ out _ H.empty21 H.arithmetic.scratch H.empty240 hr
  refine ⟨out,rf,?_,hl,hv⟩
  simpa only [DensePolynomialProgram.encode_length,hl] using hf

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
