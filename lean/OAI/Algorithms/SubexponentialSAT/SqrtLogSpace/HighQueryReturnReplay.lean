import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow

/-! The complete fixed query has an actual same-step replay after erasing its
five suspended caller words. These lemmas transport the exact output contracts
and every prefix of that execution. They do not construct a query evaluator;
the actual marked or accepted execution is supplied by the count proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HashGreedyProgram.NativeRound HighQueryEntryShadow

abbrev Data := State 40 896

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

/-- Proof-side restoration of exactly the bytes ignored by the fixed query. -/
def restore (input output : Data) : Data := rebaseState H input.stacks output

@[simp] theorem restore_regs (input output : Data) :
    (restore input output).regs = output.regs := rfl

theorem restore_visible (input output : Data) (i : Fin 896) (hi : ¬H i) :
    (restore input output).stacks i = output.stacks i :=
  rebaseStacks_of_not_mem H input.stacks output.stacks i hi

theorem restore_carried (input output : Data) (i : Fin 896) (hi : H i) :
    (restore input output).stacks i = input.stacks i :=
  rebaseStacks_of_mem H input.stacks output.stacks i hi

/-- Equality on all891 query workspace words survives restoration, including
the selector words which were erased for the source-only time proof. -/
theorem restore_workspace (input output : Data)
    (hw : HashMassAdapter.workspace output = HashMassAdapter.workspace (erase input)) :
    HashMassAdapter.workspace (restore input output) = HashMassAdapter.workspace input := by
  funext j
  let i := HashMassAdapter.workPort j
  change (restore input output).stacks i = input.stacks i
  by_cases hi : H i
  · exact restore_carried input output i hi
  · rw [restore_visible input output i hi]
    exact (congrFun hw j).trans (visible input i hi)

/-- The accepted output changes only788 in the original whole store. The
complete binary word and every opaque caller byte are retained exactly. -/
theorem restore_accepted_stacks (input output : Data) (word : List Bool)
    (hw : output.stacks = Function.update (erase input).stacks 788 word) :
    (restore input output).stacks = Function.update input.stacks 788 word := by
  funext i
  by_cases hi : H i
  · have hn : i ≠ 788 := by intro he; subst i; exact (by decide : ¬H 788) hi
    rw [restore_carried input output i hi,Function.update_of_ne hn]
  · rw [restore_visible input output i hi,hw]
    by_cases hc : i = 788
    · subst i; simp only [Function.update_self]
    · rw [Function.update_of_ne hc,Function.update_of_ne hc,visible input i hi]

/-- The parser reset survives replay, while320 is the original unread tail.
No size or content restriction is placed on that tail or accumulated mass322. -/
theorem restore_record (input output : Data)
    (hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false)
    (hb : output.stacks 321 = []) :
    RecordPrograms.state HashMassAdapter.recordPorts (restore input output)
      false true false (input.stacks 320) [] = restore input output := by
  apply RecordPrograms.state_eq_self
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2
  · exact restore_carried input output 320 (by decide)
  · exact (restore_visible input output 321 (by decide)).trans hb

/-- All actual marked prefixes, including the final halt, have the maximum
of the local workspace cap and the unchanged suspended caller-word cap. -/
theorem marked_space {k steps localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.marked k) steps (erase input) output)
    (hs : StageSpace (HighQueryProgram.marked k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    StageSpace (HighQueryProgram.marked k) (steps+1) input (max localBound frameBound) := by
  exact ⟨CommandStackTransport.eval_shadow_prefix_bound H
    (HighQueryProgram.Carried.marked_avoids k) 778 777 he
    (fun t z ht hz i _ => hs.bound t z ht hz i) hf⟩

theorem accepted_space {k steps localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.accepted k) steps (erase input) output)
    (hs : StageSpace (HighQueryProgram.accepted k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    StageSpace (HighQueryProgram.accepted k) (steps+1) input (max localBound frameBound) := by
  exact ⟨CommandStackTransport.eval_shadow_prefix_bound H
    (HighQueryProgram.Carried.accepted_avoids k) 778 777 he
    (fun t z ht hz i _ => hs.bound t z ht hz i) hf⟩

/-- The same fixed marked execution returns the canonical whole count, all
891 workspace words, both collector sources and the reset parser. Its step
count is exactly the step count of the actual shadow execution. -/
theorem marked {k steps count localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.marked k) steps (erase input) output)
    (hw : HashMassAdapter.workspace output = HashMassAdapter.workspace (erase input))
    (hp : output.regs 16 = false ∧ output.regs 17 = true ∧ output.regs 18 = false)
    (h321 : output.stacks 321 = []) (h324 : output.stacks 324 = [])
    (hcount : output.stacks 323 = countWord count)
    (hs : StageSpace (HighQueryProgram.marked k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    Eval (HighQueryProgram.marked k) steps input (restore input output) ∧
    HashMassAdapter.workspace (restore input output) = HashMassAdapter.workspace input ∧
    HashMassAdapter.read (restore input output) = HashMassAdapter.read input ∧
    RecordPrograms.state HashMassAdapter.recordPorts (restore input output)
      false true false (input.stacks 320) [] = restore input output ∧
    (restore input output).stacks 323 = countWord count ∧
    (restore input output).stacks 324 = [] ∧
    StageSpace (HighQueryProgram.marked k) (steps+1) input (max localBound frameBound) := by
  exact ⟨HighQueryProgram.Carried.marked_shadow_eval k he,
    restore_workspace input output hw,restore_carried input output 322 (by decide),
    restore_record input output hp h321,
    (restore_visible input output 323 (by decide)).trans hcount,
    (restore_visible input output 324 (by decide)).trans h324,marked_space he hs hf⟩

/-- The same fixed accepted execution changes precisely the whole count788.
The time bound needs no lengths of the five suspended caller words; their
lengths occur only in the independent maximum-prefix bound. -/
theorem accepted {k steps count localBound frameBound : ℕ} {input output : Data}
    (he : Eval (HighQueryProgram.accepted k) steps (erase input) output)
    (hw : output.stacks = Function.update (erase input).stacks 788 (countWord count))
    (hs : StageSpace (HighQueryProgram.accepted k) (steps+1) (erase input) localBound)
    (hf : ∀ i, H i → (input.stacks i).length ≤ frameBound) :
    Eval (HighQueryProgram.accepted k) steps input (restore input output) ∧
    (restore input output).stacks = Function.update input.stacks 788 (countWord count) ∧
    StageSpace (HighQueryProgram.accepted k) (steps+1) input (max localBound frameBound) := by
  exact ⟨HighQueryProgram.Carried.accepted_shadow_eval k he,
    restore_accepted_stacks input output _ hw,accepted_space he hs hf⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay
