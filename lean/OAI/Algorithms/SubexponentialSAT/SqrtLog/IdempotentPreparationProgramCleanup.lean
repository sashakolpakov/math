import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgramMetadata

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls

def clearPorts : List (Fin 41) → Cmd 8 41
  | [] => .base .skip
  | p::ps => .seq (clearAt p) (clearPorts ps)

def clearedPorts : List (Fin 41) → Data → Data
  | [],d => d
  | p::ps,d => clearedPorts ps (clearResult d p)

def clearPortsCost : List (Fin 41) → Data → ℕ
  | [],_ => 0
  | p::ps,d => 2*(d.stacks p).length+3+clearPortsCost ps (clearResult d p)

theorem clearPorts_eval (ps : List (Fin 41)) (d : Data) :
    Eval (clearPorts ps) (clearPortsCost ps d) d (clearedPorts ps d) := by
  induction ps generalizing d with
  | nil => exact .base (.skip _)
  | cons p ps ih => exact (clearAt_eval d p).seq (ih _)

theorem clearedPorts_stacks (ps : List (Fin 41)) (d : Data) (i : Fin 41) :
    (clearedPorts ps d).stacks i = if i ∈ ps then [] else d.stacks i := by
  induction ps generalizing d with
  | nil => simp [clearedPorts]
  | cons p ps ih =>
      simp only [clearedPorts,ih,List.mem_cons,clearResult]
      by_cases hi : i=p
      · subst i
        simp
      · by_cases hm : i∈ps <;> simp [hi,hm]

theorem clearPortsCost_bound (ps : List (Fin 41)) (d : Data) (W : ℕ)
    (hw : ∀ p ∈ ps, (d.stacks p).length ≤ W) :
    clearPortsCost ps d ≤ ps.length*(2*W+3) := by
  induction ps generalizing d with
  | nil => simp [clearPortsCost]
  | cons p ps ih =>
      have hp := hw p (by simp)
      have ht : ∀ q ∈ ps, ((clearResult d p).stacks q).length ≤ W := by
        intro q hq
        by_cases h : q=p
        · simp [clearResult,h]
        · simpa [clearResult,h] using hw q (by simp [hq])
      have hh := ih (clearResult d p) ht
      simp only [clearPortsCost,List.length_cons]
      nlinarith

/-- Private preparation ports are discarded before entering the Newton ABI.
The modulus, width, scalar zero, table, five arrays and two counters survive. -/
def preparationDiscard : List (Fin 41) :=
  [0,1,2,3,4,6,7,8,9,10,11,13,14,15,16,18,19,20,21,23,24,25,26,27,28,29,30,31,38,40]

abbrev preparationCleanup : Cmd 8 41 := clearPorts preparationDiscard

theorem preparationCleanup_eval (d : Data) (W : ℕ)
    (hw : ∀ p ∈ preparationDiscard, (d.stacks p).length ≤ W) :
    ∃ n e, n ≤ 30*(2*W+3) ∧ Eval preparationCleanup n d e ∧
      ∀ i, e.stacks i = if i ∈ preparationDiscard then [] else d.stacks i := by
  refine ⟨clearPortsCost preparationDiscard d,clearedPorts preparationDiscard d,
    ?_,clearPorts_eval _ _,clearedPorts_stacks _ _⟩
  exact clearPortsCost_bound preparationDiscard d W hw

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
