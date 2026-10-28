import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWorkspace
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplatePipeline
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWidePhase
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisBankOrigin
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateExecution

namespace OAI.Algorithms

/-! Exact common store shapes along the actual node worker. These equations
join the separately proved producer frames and show that the complete
worker restores every temporary cell between node visits. -/

namespace SubexponentialSAT.SubexpNodeStoreTransitions

open SubexpNodeWorkspace

def cached (masters : Store) (node cache : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (activeStacks masters node)
      100 (masters 255)) 101 (masters 126)) 66 (masters 5)) 73 (masters 91))
      74 (masters 10)) 81 (SubexpNodeCacheSetup.width4 (masters 10))) 102 cache

def indexed (masters : Store) (node cache index : List Bool) : Store :=
  Function.update (cached masters node cache) 116 index

def raw (masters : Store) (node cache index blueprint : List Bool) : Store :=
  Function.update (indexed masters node cache index) 15 blueprint

def templated (masters : Store) (index template : List Bool) : Store :=
  Function.update (Function.update (initialStacks masters) 116 index) 200 template

def jobs (masters : Store) (index stream : List Bool) : Store :=
  Function.update (Function.update (initialStacks masters) 116 index) 100 stream

theorem cached_projection (masters : Store) (node cache : List Bool) (i : Fin 256) :
    cached masters node cache (Fin.castAdd 32 i) =
      Function.update (SubexpNodeCacheSetup.preparedStacks
        (activeStacks masters node ∘ Fin.castAdd 32)) 102 cache i := by
  fin_cases i <;> rfl

theorem blueprint_result (masters : Store) (node cache index banks origins blueprint : List Bool) :
    SubexpRawTemplate.resultStore
      (SubexpNodeBasisBankOrigin.finishedStacks (indexed masters node cache index) banks origins)
        blueprint = raw masters node cache index blueprint := by
  funext i
  fin_cases i <;> rfl

theorem template_result (masters : Store) (node cache index blueprint template : List Bool) :
    SubexpNodeTemplatePipeline.resultStacks (raw masters node cache index blueprint) template =
      templated masters index template := by
  funext i
  fin_cases i <;> rfl

theorem jobs_result (masters : Store) (index template stream : List Bool) :
    Function.update (Function.update (templated masters index template) 200 []) 100 stream =
      jobs masters index stream := by
  funext i
  fin_cases i <;> rfl

theorem phase_result (masters : Store) (index stream jet shape : List Bool) :
    SubexpNodeWidePhase.resultStacks (jobs masters index stream) jet shape =
      finalStacks masters jet shape := by
  funext i
  fin_cases i <;> rfl

theorem final_restores (masters : Store) (index stream jet shape : List Bool) :
    Ready masters (Function.update (Function.update
      (SubexpNodeWidePhase.resultStacks (jobs masters index stream) jet shape) 102 []) 104 []) := by
  rw [phase_result]
  exact final_ready masters jet shape

end SubexponentialSAT.SubexpNodeStoreTransitions

end OAI.Algorithms
