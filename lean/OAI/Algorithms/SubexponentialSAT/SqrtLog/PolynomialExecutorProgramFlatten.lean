import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramBasic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgramExtract
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixContext

namespace OAI.Algorithms

/-! Generic native extraction adapter for a completed postfix interpreter. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore operandStore_frame)

abbrev flattenCommand {l : ℕ} (p : Program 16 256 l) : Code := .seq (.call p) extract
abbrev flattenProgram {l : ℕ} (p : Program 16 256 l) := compiled (flattenCommand p) 26 240

private def plainData (context : Fin 252 → List Bool) (code depth operands : List Bool) : Data :=
  ⟨fun _ => false,operandStore context code depth operands⟩

private theorem plainData_cfg {l : ℕ} (pc : Option (Fin l))
    (context : Fin 252 → List Bool) (code depth operands : List Bool) :
    (plainData context code depth operands).withPC pc =
      physicalCfg pc false false false code depth operands context := by
  apply congrArg₂ (Cfg.mk pc)
  · exact (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_false_regs pc code depth operands context).symm
  · rfl

private theorem extracted_context (context : Fin 252 → List Bool) (bits : List Bool) :
    Function.update (Function.update (Function.update
      (operandStore context [] [true] (Encoding.encodeList id [bits])) 27 []) 240 bits) 28 [] =
    Function.update (contextStore context) 240 bits := by
  funext i
  by_cases h27 : i = 27
  · subst i; simp [contextStore]
  by_cases h28 : i = 28
  · subst i; simp [contextStore]
  by_cases h240 : i = 240
  · subst i; simp
  by_cases h26 : i = 26
  · subst i
    simp [operandStore,contextStore]
  simp only [Function.update_apply,h27,h28,h240,ite_false]
  exact operandStore_frame context [] [true] (Encoding.encodeList id [bits]) i h26 h28 h27

theorem flatten_run {l : ℕ} (p : Program 16 256 l) {B d : ℕ} (context : Fin 252 → List Bool)
    (source : List Bool) (out : List (Coeff B d)) (K : ℕ)
    (h21 : contextStore context 21 = []) (h120 : contextStore context 120 = [])
    (h240 : contextStore context 240 = [])
    (hrun : RunsIn p K
      (physicalCfg (some p.entry) false false false source [] [] context)
      (physicalCfg none false false false [] (SubexpPostfixControl.operandDepth [out])
        (Encoding.encodeList DensePolynomialProgram.encode [out]) context)) :
    ∃ rf, RunsIn (flattenProgram p) (K+18*(DensePolynomialProgram.encode out).length+28)
      (physicalCfg (some (flattenProgram p).entry) false false false source [] [] context)
      ((⟨rf,Function.update (contextStore context) 240 (DensePolynomialProgram.encode out)⟩ : Data).withPC none) := by
  obtain ⟨n,hn,ht⟩ := hrun
  let bits := DensePolynomialProgram.encode out
  let s := operandStore context [] [true] (Encoding.encodeList id [bits])
  have hs (i : Fin 256) (h26 : i ≠ 26) (h28 : i ≠ 28) (h27 : i ≠ 27) :
      s i = contextStore context i := operandStore_frame context [] [true] _ i h26 h28 h27
  have hcall : Eval (.call p) n (plainData context source [] [])
      (plainData context [] [true] (Encoding.encodeList id [bits])) := by
    apply Eval.call
    change Trace p n _ _ at ht
    simpa only [plainData_cfg,SubexpPostfixControl.operandDepth,List.length_cons,List.length_nil,
      Nat.zero_add,List.replicate_succ,List.replicate_zero,bits,Encoding.encodeList,
      id_eq] using ht
  obtain ⟨m,rf,hm,he⟩ := extract_run s bits rfl rfl
    (by rw [hs 21 (by decide) (by decide) (by decide)]; exact h21)
    (SubexponentialSAT.SubexpRowPostfixInterpreter.physicalCfg_scratch _ _ _ _ _ _ _ _)
    (by rw [hs 120 (by decide) (by decide) (by decide)]; exact h120)
    (by rw [hs 240 (by decide) (by decide) (by decide)]; exact h240) (fun _ => false)
  have hfinal : Function.update (Function.update (Function.update s 27 []) 240 bits) 28 [] =
      Function.update (contextStore context) 240 bits := extracted_context context bits
  rw [hfinal] at he
  refine ⟨rf,n+m+1,by dsimp [bits] at hm; omega,?_⟩
  have h := compiled_halt_trace (hcall.seq he) 26 240
  simpa only [plainData_cfg,flattenProgram,flattenCommand,bits] using h

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
