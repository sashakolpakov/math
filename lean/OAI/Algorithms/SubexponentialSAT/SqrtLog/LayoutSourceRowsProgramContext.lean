import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
import OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixContext

namespace OAI.Algorithms

/-! Exact extraction of the native executor context from the source worker.
The four dispatcher ports are excluded from this context. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports physicalCfg contextStore)
open SubexponentialSAT.SubexpRowPostfixContext (operandStore)
attribute [local simp] Fin.coe_ofNat_eq_mod

def executionContext (s : Store) : Fin 252 → List Bool :=
  fun i => s (executorPorts (ports (Fin.natAdd 4 i)))

theorem executorStore_decompose (s : Store) (source : List Bool)
    (h26 : s 26=source) (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[]) :
    s ∘ executorPorts=operandStore (executionContext s) source [] [] := by
  funext i
  obtain ⟨j,rfl⟩ := ports.surjective i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro k
    fin_cases k <;>
      simp [operandStore,physicalCfg,SubexpPostfixGlobal.reindexCfg,
        SubexpPostfixInterpreter.cfg,SubexpPostfixControl.quadruple,
        executorPorts,Fin.addCases,h26,h27,h28,h29]
  · intro k
    simp [operandStore,physicalCfg,SubexpPostfixGlobal.reindexCfg,
      SubexpPostfixInterpreter.cfg,executionContext]

theorem evaluationInput_decompose (s : Store) (source : List Bool)
    (hsource : s 333=source.reverse)
    (h27 : s 27=[]) (h28 : s 28=[]) (h29 : s 29=[]) :
    evaluationInput s ∘ executorPorts=
      operandStore (executionContext (evaluationInput s)) source [] [] := by
  apply executorStore_decompose
  · simp [evaluationInput,hsource]
  · simp [evaluationInput,h27]
  · simp [evaluationInput,h28]
  · simp [evaluationInput,h29]

/-- The executor context discards its source and saved controls. Thus a new
postfix source on333 does not change any arithmetic readiness premise. -/
theorem executionContext_evaluation (s : Store) :
    executionContext (evaluationInput s)=executionContext (Function.update s 21 []) := by
  funext i
  let p := executorPorts (ports (Fin.natAdd 4 i))
  have hp : p.val < 256 := (ports (Fin.natAdd 4 i)).isLt
  have h26 : p≠26 := by
    intro h
    have he : ports (Fin.natAdd 4 i)=26 := by
      apply Fin.ext
      have hh := congrArg (fun k : Fin 340 => k.val) h
      change (ports (Fin.natAdd 4 i)).val=26 at hh
      exact hh
    have hi : Fin.natAdd 4 i=(0 : Fin 256) := by
      simpa using congrArg ports.symm he
    have hh := congrArg Fin.val hi
    simp at hh
  have h333 : p≠333 := by intro h; rw [h] at hp; norm_num at hp
  have h335 : p≠335 := by intro h; rw [h] at hp; norm_num at hp
  have h336 : p≠336 := by intro h; rw [h] at hp; norm_num at hp
  change evaluationInput s p=Function.update s 21 [] p
  simp [evaluationInput,Function.update_apply,h26,h333,h335,h336]

theorem executionContext_evaluation_update333 (s : Store) (bits : List Bool) :
    executionContext (evaluationInput (Function.update s 333 bits))=
      executionContext (evaluationInput s) := by
  rw [executionContext_evaluation,executionContext_evaluation]
  funext i
  have hp : (executorPorts (ports (Fin.natAdd 4 i))).val < 256 :=
    (ports (Fin.natAdd 4 i)).isLt
  have h333 : executorPorts (ports (Fin.natAdd 4 i))≠333 := by
    intro h
    rw [h] at hp
    norm_num at hp
  simp [executionContext,Function.update_apply,h333]

theorem executionContext_evaluation_congr (s t : Store)
    (h : ∀ i : Fin 340, i.val < 256 → s i=t i) :
    executionContext (evaluationInput s)=executionContext (evaluationInput t) := by
  rw [executionContext_evaluation,executionContext_evaluation]
  funext i
  have hp : (executorPorts (ports (Fin.natAdd 4 i))).val < 256 :=
    (ports (Fin.natAdd 4 i)).isLt
  simp [executionContext,Function.update_apply,h _ hp]

theorem executionContext_evaluation_rowState (s : Store) (j : ℕ) (remaining acc : List Bool) :
    executionContext (evaluationInput (rowState s j remaining acc))=
      executionContext (evaluationInput s) := by
  apply executionContext_evaluation_congr
  intro i hi
  have h320 : i≠320 := by intro h; subst i; norm_num at hi
  have h331 : i≠331 := by intro h; subst i; norm_num at hi
  have h332 : i≠332 := by intro h; subst i; norm_num at hi
  simp [rowState,h320,h331,h332]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
