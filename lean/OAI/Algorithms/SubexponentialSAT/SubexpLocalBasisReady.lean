import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalBasisState

namespace OAI.Algorithms

/-! The explicit live ports and unchanged-data frame of the batch wrapper. -/

namespace SubexponentialSAT.SubexpLocalBasisReady

open BitProgram StructuredCalls SubexpLocalBasisState

def occupied : List (Fin 131) := [107, 108, 109, 110, 111, 112, 113, 115, 116, 127, 128]

def WorkspaceReady (d : Data) : Prop := ∀ i, i ∉ occupied → d.stacks i = []

def context (d : Data) : Context where
  types := d.stacks 107
  modulus := d.stacks 108
  zero := d.stacks 109
  coefficients := d.stacks 110
  length := d.stacks 111
  colors := d.stacks 112
  positions := d.stacks 113
  slots := d.stacks 115
  alphabet := d.stacks 116

theorem ready_empty (ctx : Context) (regs : Fin 32 → Bool) (counter old : List Bool) :
    WorkspaceReady (ready ctx regs counter old) := by
  intro i
  refine Fin.addCases (m := 128) (n := 3) (fun j => ?_) (fun j => ?_) i
  · intro hi
    have hn (k : Fin 128) (hk : k.castAdd 3 ∈ occupied) : j ≠ k := by
      intro h
      subst j
      exact hi hk
    have h107 := hn 107 (by decide)
    have h108 := hn 108 (by decide)
    have h109 := hn 109 (by decide)
    have h110 := hn 110 (by decide)
    have h111 := hn 111 (by decide)
    have h112 := hn 112 (by decide)
    have h113 := hn 113 (by decide)
    have h115 := hn 115 (by decide)
    have h116 := hn 116 (by decide)
    have h127 := hn 127 (by decide)
    simp only [ready, extendState, Fin.addCases_left, Function.update_of_ne h127,
      Subexp.LocalBasisBatchProgram.inputState, ite_eq_right h107, ite_eq_right h108,
      ite_eq_right h109, ite_eq_right h110, ite_eq_right h111, ite_eq_right h112, ite_eq_right h113,
      ite_eq_right h115, ite_eq_right h116]
  · intro hi
    fin_cases j
    · exact False.elim (hi (by decide))
    · rfl
    · rfl

theorem ready_context (d : Data) (hd : WorkspaceReady d) :
    d = ready (context d) d.regs (d.stacks 128) (d.stacks 127) := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    by_cases hi : i ∈ occupied
    · simp only [occupied, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl
    · rw [ready_empty (context d) d.regs (d.stacks 128) (d.stacks 127) i hi]
      exact hd i hi

theorem result_eq_ready (ctx : Context) (counter output : List Bool) :
    result ctx counter output = ready {ctx with length := []} (fun _ => false) counter output := by
  have h114 : (Subexp.LocalBasisBatchProgram.inputState {ctx with length := []}
      (fun _ => false)).stacks 114 = [] := rfl
  have hu : Function.update
      (Subexp.LocalBasisBatchProgram.inputState {ctx with length := []} (fun _ => false)).stacks
      114 [] = (Subexp.LocalBasisBatchProgram.inputState {ctx with length := []}
        (fun _ => false)).stacks := by
    rw [← h114]
    exact Function.update_eq_self _ _
  unfold result ready Subexp.LocalBasisBatchProgram.outputState
  rw [hu]

theorem result_empty (ctx : Context) (counter output : List Bool) :
    WorkspaceReady (result ctx counter output) := by
  rw [result_eq_ready]
  exact ready_empty _ _ _ _

/-- Apart from the cleared derived length and the replaced result, every
local stack has exactly its initial contents. -/
theorem result_stacks (ctx : Context) (regs : Fin 32 → Bool)
    (counter old output : List Bool) :
    (result ctx counter output).stacks =
      Function.update (Function.update (ready ctx regs counter old).stacks 111 []) 127 output := by
  rw [result_eq_ready]
  funext i
  by_cases hi : i ∈ occupied
  · simp only [occupied, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl
  · have h111 : i ≠ 111 := by intro h; subst i; exact hi (by decide)
    have h127 : i ≠ 127 := by intro h; subst i; exact hi (by decide)
    rw [Function.update_of_ne h127, Function.update_of_ne h111,
      ready_empty _ _ _ _ i hi, ready_empty _ _ _ _ i hi]

end SubexponentialSAT.SubexpLocalBasisReady

end OAI.Algorithms
