import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramBounds

namespace OAI.Algorithms

/-! One fixed native interpreter for raw row-polynomial postfix source.
All literal padding and coefficient-array arithmetic are included. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg)

def program := SubexponentialSAT.SubexpRowPostfixInterpreter.globalProgram addProgram mulProgram
  SubexpDenseLiteralPadding.program

/-- The output is computed from the supplied source expression by native
operations. No evaluated polynomial is supplied as an input or premise. -/
theorem program_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (ops : SubexpSymbolicCost.RingProgram (Coeff (baseWidth p t) d))
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (J : ℕ)
    (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready p t M cache ops table J width frame context)
    (hB : 0 < baseWidth p t) (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (hadd : ∀ a b, (ops.addRun a b).1 =
      (RingProgram.addRun (RingProgram.scalarProgram p t M cache) a b).1)
    (hmul : ∀ a b, (ops.mulRun a b).1 =
      (RingProgram.mulRun (RingProgram.scalarProgram p t M cache) table a b).1)
    (hzero : RingProgram.flat ops.zeroRun.1 = List.replicate (d*baseWidth p t) false)
    (e : Algorithm.Expr (List (Coeff (baseWidth p t) d))) :
    RunsIn program (executionCost (addCost (baseWidth p t) d J) (mulCost (baseWidth p t) d J)
        (J*(d*baseWidth p t)) e + 5)
      (physicalCfg (some program.entry) false false false
        (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] [] context)
      (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [evaluate ops J e])
        (Encoding.encodeList DensePolynomialProgram.encode [evaluate ops J e]) context) := by
  let _ : Add (List (Coeff (baseWidth p t) d)) := ⟨addValue ops⟩
  let _ : Mul (List (Coeff (baseWidth p t) d)) := ⟨mulValue ops J⟩
  have h := SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn addProgram mulProgram
    SubexpDenseLiteralPadding.program DensePolynomialProgram.encode (loadValue ops J)
    (fun P : List (Coeff (baseWidth p t) d) => P.length = J)
    (fun _ _ => addCost (baseWidth p t) d J) (fun _ _ => mulCost (baseWidth p t) d J)
    (loadBound (baseWidth p t) d J) context
    (add_implements p t M cache ops table J width frame context H hB hadd)
    (mul_implements p t M cache ops table J width frame context H hB hz hadd hmul)
    (load_implements p t M cache ops table J width frame context H hzero)
    (validity ops J) e
  simpa only [program,executionCost_eq,← evaluate_eq ops J e] using h

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
