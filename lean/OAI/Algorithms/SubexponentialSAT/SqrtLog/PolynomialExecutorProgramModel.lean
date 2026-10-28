import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramZero

namespace OAI.Algorithms

/-! Actual arbitrary-degree RingModel semantics, with no supplied arithmetic
oracle and no supplied value of the input source expression. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg)

/-- The fixed interpreter reads source instructions, performs native arithmetic,
and leaves a framed coefficient array with the exact truncated meaning. -/
theorem model_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame context)
    (e : Algorithm.Expr (List (Coeff (baseWidth 3 t) d))) :
    ∃ out : List (Coeff (baseWidth 3 t) d),
      RunsIn program (totalBudget J e)
        (physicalCfg (some program.entry) false false false
          (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] [] context)
        (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
          (Encoding.encodeList DensePolynomialProgram.encode [out]) context) ∧
      out.length = J ∧
      meaning (RingProgram.modelRing t ht hd a M cache) out =
        Truncation.trunc J ((e.map (meaning (RingProgram.modelRing t ht hd a M cache))).eval) := by
  let ops := RingProgram.modelProgram t a M cache
  have he := program_run 3 t M cache ops (HornerProgram.modelTable t a M cache) J width frame context H
    (by rw [RingProgram.ternary_baseWidth]; omega) hz (fun _ _ => rfl) (fun _ _ => rfl)
    (DensePolynomialProgram.model_zero_bits t a M cache hz) e
  refine ⟨evaluate ops J e, he.mono (executionCost_native_polynomial J e), ?_, ?_⟩
  · exact evaluate_length ops J e
  · exact (evaluate_correct (RingProgram.modelRing t ht hd a M cache) J e).2

/-- Primitive execution inherits the fixed-table simulation constant. The
output array and its polynomial meaning are the same as for native execution. -/
theorem model_primitive (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame context)
    (e : Algorithm.Expr (List (Coeff (baseWidth 3 t) d))) :
    ∃ out : List (Coeff (baseWidth 3 t) d),
      Computation.RunsIn (primitive program).step (primitiveOverhead program * totalBudget J e)
        (primitiveCfg program (physicalCfg (some program.entry) false false false
          (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] [] context))
        (primitiveCfg program (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
          (Encoding.encodeList DensePolynomialProgram.encode [out]) context)) ∧
      out.length = J ∧
      meaning (RingProgram.modelRing t ht hd a M cache) out =
        Truncation.trunc J ((e.map (meaning (RingProgram.modelRing t ht hd a M cache))).eval) := by
  obtain ⟨out,hr,hl,hv⟩ := model_run t ht hd a M cache hz J width frame context H e
  exact ⟨out,BitProgram.primitive_execution program hr,hl,hv⟩

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
