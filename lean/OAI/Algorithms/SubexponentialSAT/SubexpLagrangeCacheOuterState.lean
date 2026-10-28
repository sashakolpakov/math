import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheState

namespace OAI.Algorithms

/-! Exact outer-loop stores. The rows are accumulated in descending label
order and reversed once by the physical finalization pass. -/

namespace SubexponentialSAT.SubexpLagrangeCacheOuterState

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpLagrangeCacheWorkspace
open SubexpLagrangeCacheState

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

def view (base : Store) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (todo : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update base
    217 (SubexpFlatAdd.encode (label p μ M zero one i))) 248 (List.replicate i false))
      250 (Subexp.FactorPacketCoordinates.cacheBytes cache)) 246 todo

omit [Fact p.Prime] in
theorem view_workspace (base : Store) (t zero one : Coefficient p μ)
    (width : List Bool) (H : Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ) base)
    (i : ℕ) (cache : List (List (List Bool))) (todo : List Bool) :
    Ready M.bits width (SubexpQuarticFlatMul.flat t) (baseWidth p μ)
      (view p μ M base zero one i cache todo) :=
  (((H.update 217 (by decide) _).update 248 (by decide) _).update 250
    (by decide) _).update 246 (by decide) _

omit [Fact p.Prime] in
theorem view_counter (base : Store) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (todo : List Bool) :
    view p μ M base zero one i cache todo 246 = todo := by simp [view]

omit [Fact p.Prime] in
theorem view_todo (base : Store) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (old todo : List Bool) :
    Function.update (view p μ M base zero one i cache old) 246 todo =
      view p μ M base zero one i cache todo := by
  simp only [view, Function.update_idem]

omit [Fact p.Prime] in
theorem view_frame (base : Store) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (todo : List Bool) (k : Fin 256)
    (h217 : k ≠ 217) (h248 : k ≠ 248) (h250 : k ≠ 250) (h246 : k ≠ 246) :
    view p μ M base zero one i cache todo k = base k := by
  simp [view, h217, h248, h250, h246]

omit [Fact p.Prime] in
theorem view_next (base : Store) (zero one : Coefficient p μ) (i : ℕ)
    (cache : List (List (List Bool))) (todo : List Bool) (row : List (List Bool)) :
    Function.update (Function.update (Function.update (view p μ M base zero one i cache todo)
      250 (Subexp.FactorPacketCoordinates.cacheBytes (row :: cache)))
        217 (SubexpFlatAdd.encode (label p μ M zero one (i + 1))))
          248 (false :: List.replicate i false) =
      view p μ M base zero one (i + 1) (row :: cache) todo := by
  funext k
  by_cases h217 : k = 217
  · subst k; simp [view]
  · by_cases h248 : k = 248
    · subst k; simp [view, List.replicate_succ]
    · by_cases h250 : k = 250
      · subst k; simp [view]
      · simp [view, Function.update_apply, h217, h248, h250]

omit [Fact p.Prime] in
theorem inner_finished (base : Store) (zero one : Coefficient p μ)
    (D j : ℕ) (a : Partial p μ D)
    (h218 : base 218 = []) (h247 : base 247 = []) (h249 : base 249 = []) :
    Function.update (Function.update (SubexpLagrangeCacheState.view p μ M D base zero one j a [])
      218 []) 249 [] =
      Function.update (Function.update base 205 (SubexpFlatAdd.encode a.denominator))
        240 (encode p μ a.polynomial) := by
  funext k
  by_cases h218' : k = 218
  · subst k; simp [SubexpLagrangeCacheState.view, h218]
  · by_cases h247' : k = 247
    · subst k; simp [SubexpLagrangeCacheState.view, h247]
    · by_cases h249' : k = 249
      · subst k; simp [SubexpLagrangeCacheState.view, h249]
      · simp [SubexpLagrangeCacheState.view, Function.update_apply, h218', h247', h249']

end SubexponentialSAT.SubexpLagrangeCacheOuterState

end OAI.Algorithms
