import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeTemplateReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodeStoreTransitions

namespace OAI.Algorithms

/-! The two source-construction contexts are read from the physical masters.
The canonical store equations establish every scratch premise of the
template and job stages; no prepared-state equality is an extra input. -/

namespace SubexponentialSAT.SubexpNodeContexts

open BitProgram StructuredCalls SubexpNodeWorkspace SubexpNodeStoreTransitions

def templateContext (masters : Store) (D : ℕ) : SubexpTemplateProgram.Context where
  sourceModulus := masters 128
  sourceReduction := masters 130
  sourceWidth := masters 129
  targetWidth := masters 10
  sourceZero := masters 131
  pointStream := []
  targetModulus := masters 5
  targetMinusOne := masters 121
  dimension := D
  indexWidth := SubexpSymbolicCost.indexBits D

def sourceContext (masters : Store) (D : ℕ) (template : List Bool) :
    SubexpMomentSourceProgram.Context where
  exponent := []
  width := masters 129
  target := masters 10
  modulus := masters 5
  unit := masters 124
  dimension := D
  indexWidth := SubexpSymbolicCost.indexBits D
  zero := masters 122
  one := masters 123
  template := template

theorem raw_template_work (masters : Store) (node cache index blueprint : List Bool)
    (i : Fin 142) (hi : i ≠ 130) :
    raw masters node cache index blueprint
      (Fin.castAdd 32 (SubexpNodeTemplateStage.port i)) = [] := by
  fin_cases i <;> first | exact False.elim (hi rfl) | rfl

theorem template_ready (masters : Store) (D : ℕ) (node cache index blueprint : List Bool)
    (hD : masters 109 = List.replicate D true)
    (hI : masters 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (d : State 16 256)
    (hs : d.stacks = raw masters node cache index blueprint ∘ Fin.castAdd 32) :
    SubexpNodeTemplateReady.Ready d (templateContext masters D) blueprint := by
  constructor
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; exact hD
  · rw [hs]; exact hI
  · rw [hs]; rfl
  · intro i hi
    rw [hs]
    exact raw_template_work masters node cache index blueprint i hi

theorem templated_source_work (masters : Store) (index template : List Bool)
    (i : Fin 63) (hi : i ≠ 62) :
    templated masters index template
      (Fin.castAdd 32 (SubexpNodeJobsReady.sourcePort i)) = [] := by
  fin_cases i <;> first | exact False.elim (hi rfl) | rfl

theorem jobs_ready (masters : Store) (D : ℕ) (index template : List Bool)
    (hD : masters 109 = List.replicate D true)
    (hI : masters 92 = List.replicate (SubexpSymbolicCost.indexBits D) true)
    (d : State 16 256)
    (hs : d.stacks = templated masters index template ∘ Fin.castAdd 32) :
    SubexpNodeJobsReady.Ready d (sourceContext masters D template) := by
  constructor
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; exact hD
  · rw [hs]; exact hI
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rw [hs]; rfl
  · rfl
  · rw [hs]; rfl
  · intro i hi
    rw [hs]
    exact templated_source_work masters index template i hi

end SubexponentialSAT.SubexpNodeContexts

end OAI.Algorithms
