import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

/-! Retained integer caches are replaced at every node. This paid reset must
precede the original bootstrap's append-copy retention step. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeCaches

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

def cleared (port : Fin 768) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks port []⟩

theorem clear_eval (port : Fin 768) (a : Data) :
    Eval (clear port) (2*(a.stacks port).length+3) a (cleared port a) := by
  apply Eval.call
  exact ListRegisterProgram.clear_run port (0 : Fin 40) 1 a.regs a.stacks

def resetCaches : Code := .seq (clear 710) (.seq (clear 711) (clear 712))

def resetState (a : Data) : Data := cleared 712 (cleared 711 (cleared 710 a))

def resetCost (a : Data) : ℕ :=
  2*((a.stacks 710).length+(a.stacks 711).length+(a.stacks 712).length)+9

theorem reset_eval (a : Data) : Eval resetCaches (resetCost a) a (resetState a) := by
  have he := (clear_eval 710 a).seq
    ((clear_eval 711 (cleared 710 a)).seq (clear_eval 712 (cleared 711 (cleared 710 a))))
  convert he using 1
  · rfl
  · simp [resetCost, cleared]
    omega
  · rfl

theorem reset_stacks (a : Data) :
    (resetState a).stacks =
      Function.update (Function.update (Function.update a.stacks 710 []) 711 []) 712 [] := rfl

theorem reset_empty (a : Data) :
    (resetState a).stacks 710 = [] ∧ (resetState a).stacks 711 = [] ∧
    (resetState a).stacks 712 = [] := by
  simp [reset_stacks]

theorem reset_frame (a : Data) (i : Fin 768)
    (h710 : i ≠ 710) (h711 : i ≠ 711) (h712 : i ≠ 712) :
    (resetState a).stacks i = a.stacks i := by
  simp [reset_stacks, h710, h711, h712]

theorem reset_boundary (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((resetState a).stacks i).length ≤ B := by
  intro i
  by_cases h710 : i = 710
  · subst i; simp [reset_empty]
  by_cases h711 : i = 711
  · subst i; simp [reset_empty]
  by_cases h712 : i = 712
  · subst i; simp [reset_empty]
  rw [reset_frame a i h710 h711 h712]
  exact ha i

theorem reset_cost_le (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    resetCost a ≤ 6*B+9 := by
  have := ha 710
  have := ha 711
  have := ha 712
  unfold resetCost
  omega

/-- Every stack, including the caller frame, is counted at every prefix. -/
theorem reset_resources (a : Data) :
    Trace (compiled resetCaches 300 78) (resetCost a+1)
      (a.withPC (some (compiled resetCaches 300 78).entry)) ((resetState a).withPC none) ∧
    ∀ prefixSteps intermediate, prefixSteps ≤ resetCost a+1 →
      Trace (compiled resetCaches 300 78) prefixSteps
        (a.withPC (some (compiled resetCaches 300 78).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ stackBits a.stacks+resetCost a :=
  RingNodeSetup.eval_resources (reset_eval a) 300 78

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeCaches
