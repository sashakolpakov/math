import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayFootprint
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! All-prefix resource transport for the existing exact-time tape replay.
The imported avoidance certificate excludes reads as well as writes, including
`peek`. Erasing hidden caller data is a proof construction only: the actual
instruction table and its measured number of steps remain unchanged. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

variable {r s l : ℕ}

theorem rebaseState_restore (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : State r s) :
    rebaseState H a.stacks (rebaseState H frame a) = a := by
  cases a with
  | mk regs words =>
      apply congrArg (fun ws => (⟨regs, ws⟩ : State r s))
      funext i
      by_cases hi : H i <;> simp [rebaseState, rebaseStacks, hi]

theorem rebaseCfg_restore (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : Cfg r s l) :
    rebaseCfg H a.stacks (rebaseCfg H frame a) = a := by
  cases a with
  | mk pc regs words =>
      apply congrArg (fun ws => (⟨pc, regs, ws⟩ : Cfg r s l))
      funext i
      by_cases hi : H i <;> simp [rebaseCfg, rebaseStacks, hi]

/-- A concrete parameter bank disjoint from hidden storage is unchanged by
the proof-only shadow projection. Registers are always retained. -/
theorem projectState_rebase {R S : ℕ} (H : Fin S → Prop) [DecidablePred H]
    (frame : Fin S → List Bool) (a : State R S)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hstack : ∀ i, ¬ H (stack i)) :
    projectState register stack (rebaseState H frame a) = projectState register stack a := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    exact rebaseStacks_of_not_mem H frame a.stacks (stack i) (hstack i)

/-- The shadow state retains only visible inputs. Its storage bound does not
contain the size of the hidden collector or incumbent. -/
theorem shadow_stack_bound (H : Fin s → Prop) [DecidablePred H]
    (a : State r s) (bound : ℕ)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ bound) :
    ∀ i, ((rebaseState H (fun _ => []) a).stacks i).length ≤ bound := by
  intro i
  by_cases hi : H i
  · simp [rebaseState, rebaseStacks, hi]
  · simpa only [rebaseState, rebaseStacks_of_not_mem H (fun _ => []) a.stacks i hi]
      using ha i hi

/-- An arbitrary prefix of the rebased execution is the rebase of the exact
same-length prefix of the original execution. -/
theorem trace_prefix_rebase (H : Fin s → Prop) [DecidablePred H]
    {p : Program r s l} (hp : AvoidsProgram H p)
    (frame : Fin s → List Bool) {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (ht : Trace p steps a b) {intermediate : Cfg r s l}
    (hle : prefixSteps ≤ steps)
    (hprefix : Trace p prefixSteps (rebaseCfg H frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = rebaseCfg H frame source := by
  obtain ⟨source, hs⟩ := trace_prefix_exists ht hle
  exact ⟨source, hs, trace_same_length_unique hprefix (trace_rebase H hp hs frame)⟩

/-- Only hidden caller stacks contribute the frame bound. Every visible stack
is controlled by the actual local trace, with no multiplicative recurrence. -/
theorem trace_stack_bound (H : Fin s → Prop) [DecidablePred H]
    {p : Program r s l} (hp : AvoidsProgram H p)
    (frame : Fin s → List Bool) {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (ht : Trace p steps a b)
    (hsource : ∀ prefixSteps source, prefixSteps ≤ steps →
      Trace p prefixSteps a source →
      ∀ i, ¬ H i → (source.stacks i).length ≤ bound)
    (hframe : ∀ i, H i → (frame i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps (rebaseCfg H frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hprefix i
  obtain ⟨source, hs, rfl⟩ := trace_prefix_rebase H hp frame ht hle hprefix
  by_cases hi : H i
  · change (rebaseStacks H frame source.stacks i).length ≤ _
    rw [rebaseStacks_of_mem H frame source.stacks i hi]
    exact (hframe i hi).trans (Nat.le_max_right _ _)
  · change (rebaseStacks H frame source.stacks i).length ≤ _
    rw [rebaseStacks_of_not_mem H frame source.stacks i hi]
    exact (hsource prefixSteps source hle hs i hi).trans (Nat.le_max_left _ _)

/-- A local execution on the empty hidden shadow yields an execution of the
same fixed command on the actual caller, at exactly the same step count. -/
theorem eval_shadow (H : Fin s → Prop) [DecidablePred H]
    {command : Cmd r s} (hc : AvoidsCmd H command)
    {steps : ℕ} {a b : State r s}
    (he : Eval command steps (rebaseState H (fun _ => []) a) b) :
    Eval command steps a (rebaseState H a.stacks b) := by
  have h := eval_rebase H hc he a.stacks
  rw [rebaseState_restore] at h
  exact h

/-- The local all-prefix bound is transported through the compiled command,
including its final halt. Hidden external words are restored unchanged. -/
theorem eval_shadow_prefix_bound (H : Fin s → Prop) [DecidablePred H]
    {command : Cmd r s} (hc : AvoidsCmd H command) (input output : Fin s)
    {steps bound frameBound : ℕ} {a b : State r s}
    (he : Eval command steps (rebaseState H (fun _ => []) a) b)
    (hsource : ∀ prefixSteps source, prefixSteps ≤ steps + 1 →
      Trace (compiled command input output) prefixSteps
        ((rebaseState H (fun _ => []) a).withPC
          (some (compiled command input output).entry)) source →
      ∀ i, ¬ H i → (source.stacks i).length ≤ bound)
    (hframe : ∀ i, H i → (a.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (compiled command input output) prefixSteps
        (a.withPC (some (compiled command input output).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  have h := trace_stack_bound H (avoids_compiled H command hc input output)
    a.stacks (compiled_halt_trace he input output) hsource hframe
  rw [rebaseCfg_withPC, rebaseState_restore] at h
  exact h

/-- Hidden caller words are preserved at every prefix of this same replayed
execution, including prefixes within called finite instruction tables. -/
theorem eval_shadow_prefix_frame (H : Fin s → Prop) [DecidablePred H]
    {command : Cmd r s} (hc : AvoidsCmd H command) (input output : Fin s)
    {steps : ℕ} {a b : State r s}
    (he : Eval command steps (rebaseState H (fun _ => []) a) b)
    {prefixSteps : ℕ} {intermediate : Cfg r s (size command + 1)}
    (hle : prefixSteps ≤ steps + 1)
    (hprefix : Trace (compiled command input output) prefixSteps
      (a.withPC (some (compiled command input output).entry)) intermediate)
    (i : Fin s) (hi : H i) : intermediate.stacks i = a.stacks i := by
  have hstart : rebaseCfg H a.stacks
      ((rebaseState H (fun _ => []) a).withPC
        (some (compiled command input output).entry)) =
      a.withPC (some (compiled command input output).entry) := by
    rw [rebaseCfg_withPC, rebaseState_restore]
  rw [← hstart] at hprefix
  obtain ⟨source, _, rfl⟩ := trace_prefix_rebase H
    (avoids_compiled H command hc input output) a.stacks
    (compiled_halt_trace he input output) hle hprefix
  exact rebaseStacks_of_mem H a.stacks source.stacks i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
