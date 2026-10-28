import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowAssemblyExecution

namespace OAI.Algorithms

/-! The row bound ignores caller registers, parser tails and accumulators. -/

namespace SubexponentialSAT.Subexp.UniversalRowAssembly

open BitProgram StructuredCalls StackRoutines
open UniversalRowWorkspace (port port_injective)

def boundInputPorts : List (Fin 288) :=
  [128, 129, 131, 132, 133, 134, 135, 136, 137, 243, 252, 253, 254, 272, 275, 284]

def SameBoundInputs (a b : Data) : Prop :=
  ∀ j ∈ boundInputPorts, a.stacks j = b.stacks j

private def relevant (j : Fin 288) : Prop := (∃ k, port k = j) ∨ j ∈ boundInputPorts

private def agree (s t : Fin 288 → Word) : Prop := ∀ j, relevant j → s j = t j

private theorem relevant_port (j : Fin 49) : relevant (port j) := Or.inl ⟨j, rfl⟩

private theorem relevant_master (j : Fin 288) (h : j ∈ boundInputPorts) : relevant j := Or.inr h

private theorem master_disjoint (j : Fin 288) (hj : j ∈ boundInputPorts) :
    ¬ ∃ k, port k = j := by
  have hhigh : 128 ≤ j.val := by
    simp only [boundInputPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  rintro ⟨k, rfl⟩
  have := UniversalRowWorkspace.port_lt_cache k
  omega

private theorem agree_update {s t : Fin 288 → Word} (h : agree s t)
    (j : Fin 288) (x y : Word) (hxy : x = y) :
    agree (Function.update s j x) (Function.update t j y) := by
  intro k hk
  by_cases hkj : k = j
  · subst k
    simpa using hxy
  · simpa [hkj] using h k hk

private theorem setup_congr (a b : Data) (h : SameBoundInputs a b) (Q r R w : ℕ) :
    UniversalRowInputSetup.inputStacks a Q r R w =
      UniversalRowInputSetup.inputStacks b Q r R w := by
  have hsource (j : Fin 49) : a.stacks (UniversalRowInputSetup.source j) =
      b.stacks (UniversalRowInputSetup.source j) := by
    apply h
    unfold UniversalRowInputSetup.source
    split_ifs <;> decide
  have hs : UniversalRowInputSetup.seedNative a = UniversalRowInputSetup.seedNative b := by
    funext j
    unfold UniversalRowInputSetup.seedNative
    split_ifs
    · exact hsource j
    · rfl
  simp only [UniversalRowInputSetup.inputStacks, hs]

variable {r Q Δ : ℕ}
variable (p : ℕ) [Fact p.Prime] (i : Fin Δ)
variable (u y : MulticolorTypes.UniversalType r Q Δ) (xs : List (ZMod p))

omit [Fact p.Prime] in
private theorem staged_agree (a b : Data) (h : SameBoundInputs a b) :
    agree (stagedStacks (r := r) (Q := Q) p xs a) (stagedStacks (r := r) (Q := Q) p xs b) := by
  intro j hj
  rcases hj with ⟨k, rfl⟩ | hj
  · simp only [stagedStacks, port_injective.extend_apply]
    exact congrFun (setup_congr a b h Q r xs.length (MatrixWordEncoding.width p)) k
  · have hn := master_disjoint j hj
    simp only [stagedStacks, Function.extend_apply' _ _ _ hn]
    exact h j hj

theorem deltaWord_congr (a b : Data) (h : SameBoundInputs a b) :
    deltaWord u y a = deltaWord u y b := by
  simp only [deltaWord, h 131 (by decide), h 132 (by decide)]

omit [Fact p.Prime] in
theorem sourceWord_congr (t : UniversalRowLoop.Tables) (a b : Data) (h : SameBoundInputs a b) :
    sourceWord p i u y xs t a = sourceWord p i u y xs t b := by
  simp only [sourceWord, h 131 (by decide), h 132 (by decide), deltaWord_congr u y a b h]

private theorem before_agree (a b : Data) (h : SameBoundInputs a b) :
    agree (beforeData p i u y xs a).stacks (beforeData p i u y xs b).stacks := by
  unfold beforeData
  apply agree_update
  · apply agree_update _ _ _ _ rfl
    apply agree_update _ _ _ _ rfl
    apply agree_update
    · apply agree_update _ _ _ _ rfl
      apply agree_update _ _ _ _ rfl
      exact staged_agree p xs a b h
    · exact h 132 (by decide)
  · exact deltaWord_congr u y a b h

private def inputPort : UniversalRowRearrange.Action → Fin 288
  | .copy src _ => src
  | .clear dst => port dst

private theorem operation_inputs :
    ∀ op ∈ UniversalRowRearrange.operations, relevant (inputPort op) := by
  intro op hop
  simp only [UniversalRowRearrange.operations, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact relevant_port _ | exact relevant_master _ (by decide)

private theorem action_agree (op : UniversalRowRearrange.Action) (a b : Data)
    (h : agree a.stacks b.stacks) (hop : relevant (inputPort op)) :
    agree (UniversalRowRearrange.actionResult op a).stacks
      (UniversalRowRearrange.actionResult op b).stacks := by
  cases op with
  | copy src dst =>
      apply agree_update h
      exact congrArg₂ (· ++ ·) (h src hop) (h (port dst) (relevant_port dst))
  | clear dst => exact agree_update h _ _ _ rfl

private theorem result_agree (os : List UniversalRowRearrange.Action) (a b : Data)
    (h : agree a.stacks b.stacks) (hos : ∀ op ∈ os, relevant (inputPort op)) :
    agree (UniversalRowRearrange.result os a).stacks
      (UniversalRowRearrange.result os b).stacks := by
  induction os generalizing a b with
  | nil => exact h
  | cons op os ih =>
      apply ih (UniversalRowRearrange.actionResult op a) (UniversalRowRearrange.actionResult op b)
        (action_agree op a b h (hos op (by simp)))
      intro c hc
      exact hos c (by simp [hc])

private theorem cost_agree (os : List UniversalRowRearrange.Action) (a b : Data)
    (h : agree a.stacks b.stacks) (hos : ∀ op ∈ os, relevant (inputPort op)) :
    UniversalRowRearrange.cost os a = UniversalRowRearrange.cost os b := by
  induction os generalizing a b with
  | nil => rfl
  | cons op os ih =>
      have hinput := h (inputPort op) (hos op (by simp))
      have hc : UniversalRowRearrange.actionCost op a = UniversalRowRearrange.actionCost op b := by
        cases op <;> simp only [inputPort] at hinput <;>
          simp only [UniversalRowRearrange.actionCost, hinput]
      have ht := ih (UniversalRowRearrange.actionResult op a) (UniversalRowRearrange.actionResult op b)
        (action_agree op a b h (hos op (by simp)))
        (fun c hc => hos c (by simp [hc]))
      simp only [UniversalRowRearrange.cost, hc, ht]

private theorem after_agree (a b : Data) (h : SameBoundInputs a b) :
    agree (afterData p i u y xs a).stacks (afterData p i u y xs b).stacks :=
  result_agree UniversalRowRearrange.operations (beforeData p i u y xs a) (beforeData p i u y xs b)
    (before_agree p i u y xs a b h) operation_inputs

private theorem moved_agree (t : UniversalRowLoop.Tables) (a b : Data) (h : SameBoundInputs a b) :
    agree (afterMove p i u y xs t a).stacks (afterMove p i u y xs t b).stacks := by
  unfold afterMove afterEmit
  apply agree_update
  · apply agree_update _ _ _ _ rfl
    apply agree_update _ _ _ _ rfl
    apply agree_update
    · apply agree_update _ _ _ _ rfl
      exact after_agree p i u y xs a b h
    · exact sourceWord_congr p i u y xs t a b h
  · exact sourceWord_congr p i u y xs t a b h

private theorem clearCost_agree (js : List (Fin 288)) (a b : Data)
    (h : agree a.stacks b.stacks) (hjs : ∀ j ∈ js, relevant j) :
    UniversalRowWorkspace.clearCost js a = UniversalRowWorkspace.clearCost js b := by
  induction js generalizing a b with
  | nil => rfl
  | cons j js ih =>
      have hj := h j (hjs j (by simp))
      have ht := ih (UniversalRowWorkspace.cleared a j) (UniversalRowWorkspace.cleared b j)
        (agree_update h j [] [] rfl) (fun k hk => hjs k (by simp [hk]))
      simp only [UniversalRowWorkspace.clearCost, hj, ht]

/-- Changes to registers or stacks outside this fixed list do not change
the bound, including changes to every high parser tail and output table. -/
theorem executionBound_congr (t : UniversalRowLoop.Tables) (a b : Data)
    (h : SameBoundInputs a b) :
    executionBound p i u y xs t a = executionBound p i u y xs t b := by
  have hsetup : UniversalRowInputSetup.budget a Q r (MatrixWordEncoding.width p) =
      UniversalRowInputSetup.budget b Q r (MatrixWordEncoding.width p) := by
    simp only [UniversalRowInputSetup.budget_eq,
      h 252 (by decide), h 253 (by decide), h 272 (by decide), h 275 (by decide),
      h 284 (by decide), h 128 (by decide), h 254 (by decide), h 243 (by decide),
      h 133 (by decide), h 131 (by decide)]
  have hrearrange := cost_agree UniversalRowRearrange.operations
    (beforeData p i u y xs a) (beforeData p i u y xs b) (before_agree p i u y xs a b h) operation_inputs
  have hclear := clearCost_agree UniversalRowWorkspace.workPorts
    (afterMove p i u y xs t a) (afterMove p i u y xs t b)
    (moved_agree p i u y xs t a b h) (by
      intro j hj
      obtain ⟨k, hk⟩ := (UniversalRowWorkspace.mem_workPorts j).mp hj
      exact Or.inl ⟨k, hk⟩)
  simp only [executionBound, hsetup, hrearrange, hclear,
    h 131 (by decide), h 132 (by decide), h 134 (by decide),
    deltaWord_congr u y a b h, sourceWord_congr p i u y xs t a b h]

end SubexponentialSAT.Subexp.UniversalRowAssembly

end OAI.Algorithms
