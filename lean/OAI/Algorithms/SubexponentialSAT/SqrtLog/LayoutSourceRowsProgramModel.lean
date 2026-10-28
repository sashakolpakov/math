import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramContext
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramFlat

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

private theorem clear_operandSource (context : Fin 252 → List Bool) (source : List Bool) :
    Function.update (operandStore context source [] []) 26 []=contextStore context := by
  funext i
  by_cases h26 : i=26
  · subst i; simp [contextStore]
  by_cases h28 : i=28
  · subst i; simp [operandStore,contextStore]
  by_cases h27 : i=27
  · subst i; simp [operandStore,contextStore]
  simp only [Function.update_apply,h26,ite_false]
  exact operandStore_frame context source [] [] i h26 h28 h27

private theorem input_cfg {l : ℕ} (pc : Option (Fin l))
    (context : Fin 252 → List Bool) (source : List Bool) :
    ((⟨fun _ => false,operandStore context source [] []⟩ : State 16 256).withPC pc)=
      physicalCfg pc false false false source [] [] context := by
  apply congrArg₂ (Cfg.mk pc)
  · exact (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_false_regs pc source [] [] context).symm
  · rfl

def executeModel : Code := execute PolynomialExecutorProgram.flatProgram

theorem executeModel_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (context : Fin 252 → List Bool)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame context)
    (e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)))
    (s : Store)
    (hs : s ∘ executorPorts=operandStore context
      (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile) [] []) :
    ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), out.length=J ∧
      PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc J ((e.map (PolynomialExecutorProgram.meaning
          (RingProgram.modelRing t ht hd a M cache))).eval) ∧
      ExecutesIn executeModel
        (PolynomialExecutorProgram.totalBudget J e+18*(J*(d*baseWidth 3 t))+46) s
        (Function.update (Function.update s 26 []) 240 (DensePolynomialProgram.encode out)) := by
  obtain ⟨out,rf,hrun,hlen,hmeaning⟩ :=
    PolynomialExecutorProgram.model_flat_run t ht hd a M cache hz J width frame context H e
  refine ⟨out,hlen,hmeaning,?_⟩
  have hh : ∃ rf, RunsIn PolynomialExecutorProgram.flatProgram
      (PolynomialExecutorProgram.totalBudget J e+18*(J*(d*baseWidth 3 t))+28)
      ((⟨fun _ => false,s ∘ executorPorts⟩ : State 16 256).withPC
        (some PolynomialExecutorProgram.flatProgram.entry))
      ((⟨rf,Function.update (Function.update (s ∘ executorPorts) 26 []) 240
        (DensePolynomialProgram.encode out)⟩ : State 16 256).withPC none) := by
    refine ⟨rf,?_⟩
    rw [hs,clear_operandSource,input_cfg]
    exact hrun
  have h := execute_run PolynomialExecutorProgram.flatProgram _ s _ hh
  simpa [executeModel,Nat.add_assoc] using h

/-- The source byte count controls the full native interpretation cost.
Both source-generation controls are restored before returning the array. -/
theorem evaluateModel_run (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (J : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) (s : Store)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) J width frame
        (executionContext (evaluationInput s)))
    (e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)))
    (hsource : s 333=(SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).reverse)
    (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[])
    (h335 : s 335=[]) (h336 : s 336=[]) :
    ∃ out : List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d), out.length=J ∧
      PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc J ((e.map (PolynomialExecutorProgram.meaning
          (RingProgram.modelRing t ht hd a M cache))).eval) ∧
      ExecutesIn (evaluateRow PolynomialExecutorProgram.flatProgram)
        (300000*((s 333).length+1)*(J+1)^3*(d+1)^3*(baseWidth 3 t+1)^2+
          18*(J*(d*baseWidth 3 t))+46+6*(s 21).length+6*(s 26).length+
          3*(s 333).length+15) s
        (Function.update (Function.update s 333 []) 240 (DensePolynomialProgram.encode out)) := by
  obtain ⟨out,hlen,hmeaning,hcore⟩ := executeModel_run t ht hd a M cache hz J width frame
    (executionContext (evaluationInput s)) H e (evaluationInput s)
    (evaluationInput_decompose s _ hsource h27 h28 h29)
  refine ⟨out,hlen,hmeaning,?_⟩
  have hr := evaluateRow_run PolynomialExecutorProgram.flatProgram _ s
    (DensePolynomialProgram.encode out) h335 h336 hcore
  apply hr.mono
  have hb := PolynomialExecutorProgram.totalBudget_le_source J e
  have hl : (s 333).length=
      (SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile).length := by
    simp [hsource]
  rw [←hl] at hb
  omega

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
