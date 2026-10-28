import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArrayUpdatePrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

namespace OAI.Algorithms

/-!
# A temporary candidate assignment with fixed control

The current assignment, candidate word, processed-position counter, and width
are preserved. The program copies the assignment and replaces precisely the
processed word in that copy. No restore of the original assignment is needed.
-/

namespace SubexponentialSAT.Subexp.CandidateArrayProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 2 10

abbrev state (regs : Fin 2 → Bool) (original candidate index width work indexWork : List Bool) : Data :=
  ⟨regs, ![original, candidate, index, width, [], [], [], [], work, indexWork]⟩

def replacePorts : Fin 8 → Fin 10 := ![8, 1, 9, 3, 4, 5, 6, 7]

theorem replacePorts_injective : Function.Injective replacePorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [replacePorts]

abbrev replace : Cmd 2 10 := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1) id replacePorts)

abbrev command : Cmd 2 10 :=
  .seq (.call (copyProgram 0 8 4 (0 : Fin 2) 1))
    (.seq (.call (copyProgram 2 9 4 (0 : Fin 2) 1)) replace)

abbrev program : Program 2 10 (size command + 1) := compiled command 0 8

private theorem state_ext {a b : Data} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; cases hr; cases hs; rfl

private theorem embed_replace_eq (frame target : Data) (inner : State 2 8)
    (hr : ∀ i, target.regs i = inner.regs i)
    (hs : ∀ i, target.stacks (replacePorts i) = inner.stacks i)
    (hf : ∀ j, (¬ ∃ i, replacePorts i = j) → target.stacks j = frame.stacks j) :
    embedState id replacePorts frame inner = target := by
  apply state_ext
  · funext j
    exact (show (embedState id replacePorts frame inner).regs j = inner.regs j by
      simpa only [id_eq] using
        embedState_register id replacePorts frame inner Function.injective_id j).trans (hr j).symm
  · funext j
    by_cases hj : ∃ i, replacePorts i = j
    · obtain ⟨i, rfl⟩ := hj
      exact (embedState_stack id replacePorts frame inner replacePorts_injective i).trans (hs i).symm
    · exact (embedState_stack_frame id replacePorts frame inner j hj).trans (hf j hj).symm

theorem copy_array_eval (regs : Fin 2 → Bool)
    (original candidate index width : List Bool) :
    Eval (.call (copyProgram 0 8 4 (0 : Fin 2) 1)) (7 * original.length + 5)
      (state regs original candidate index width [] [])
      (state (readRegs regs 0 1 none) original candidate index width original []) := by
  have h := TupleProgram.copy_eval (0 : Fin 10) 8 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (state regs original candidate index width [] []) (by rfl)
  have he : (⟨readRegs (state regs original candidate index width [] []).regs 0 1 none,
      copyStacks 0 8 (state regs original candidate index width [] []).stacks⟩ : Data) =
      state (readRegs regs 0 1 none) original candidate index width original [] := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> simp [ copyStacks]
  rw [he] at h
  simpa [state] using h

theorem copy_index_eval (regs : Fin 2 → Bool)
    (original candidate index width work : List Bool) :
    Eval (.call (copyProgram 2 9 4 (0 : Fin 2) 1)) (7 * index.length + 5)
      (state regs original candidate index width work [])
      (state (readRegs regs 0 1 none) original candidate index width work index) := by
  have h := TupleProgram.copy_eval (2 : Fin 10) 9 4 (0 : Fin 2) 1
    (by decide) (by decide) (by decide) (by decide)
    (state regs original candidate index width work []) (by rfl)
  have he : (⟨readRegs (state regs original candidate index width work []).regs 0 1 none,
      copyStacks 2 9 (state regs original candidate index width work []).stacks⟩ : Data) =
      state (readRegs regs 0 1 none) original candidate index width work index := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> simp [ copyStacks]
  rw [he] at h
  simpa [state] using h

theorem replace_eval (regs : Fin 2 → Bool) (original : List Bool)
    (before : List (List Bool)) (old candidate rest index width : List Bool)
    (hi : index.length = before.length)
    (hrows : ∀ row ∈ before, row.length = width.length)
    (ho : old.length = width.length) (hc : candidate.length = width.length) :
    Eval replace (before.length * (14 * width.length + 10) + 20 * width.length + 21)
      (state regs original candidate index width (before.flatten ++ (old ++ rest)) index)
      (state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) []) := by
  let inner : State 2 8 := ⟨regs,
    ![before.flatten ++ (old ++ rest), candidate, index, width, [], [], [], []]⟩
  let base := state regs original candidate index width (before.flatten ++ (old ++ rest)) index
  have ht := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 2) 1 (by decide)
    before old candidate rest width index regs inner.stacks
    rfl rfl rfl rfl hi hrows ho hc rfl rfl rfl rfl
  change Trace (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1) _
    (inner.withPC (some (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1).entry))
    ((⟨readRegs regs 0 1 none,
      ArrayUpdatePrograms.replaceStacks before candidate rest inner.stacks⟩ : State 2 8).withPC none) at ht
  have he := eval_call_lifted (ArrayUpdatePrograms.replaceProgram (0 : Fin 2) 1)
    id replacePorts base Function.injective_id replacePorts_injective ht
  have hin : embedState id replacePorts base inner = base := by
    apply embed_replace_eq
    · intro j; rfl
    · intro j; fin_cases j <;> rfl
    · intro j hj; rfl
  have hout : embedState id replacePorts base
      (⟨readRegs regs 0 1 none,
        ArrayUpdatePrograms.replaceStacks before candidate rest inner.stacks⟩ : State 2 8) =
      state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) [] := by
    apply embed_replace_eq
    · intro j; rfl
    · intro j; fin_cases j <;> simp [replacePorts, inner, ArrayUpdatePrograms.replaceStacks]
    · intro j hj
      fin_cases j <;> simp_all [replacePorts, base, inner, state, Fin.exists_fin_succ]
  simpa only [hin, hout, replace, inner, base] using he

def sourceCost (originalSize position width : ℕ) : ℕ :=
  7 * originalSize + 7 * position + position * (14 * width + 10) + 20 * width + 32

theorem command_eval (regs : Fin 2 → Bool) (before : List (List Bool))
    (old candidate rest index width : List Bool)
    (hi : index.length = before.length)
    (hrows : ∀ row ∈ before, row.length = width.length)
    (ho : old.length = width.length) (hc : candidate.length = width.length) :
    let original := before.flatten ++ (old ++ rest)
    Eval command (sourceCost original.length before.length width.length - 1)
      (state regs original candidate index width [] [])
      (state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) []) := by
  dsimp only
  have h := (copy_array_eval regs (before.flatten ++ (old ++ rest)) candidate index width).seq
    ((copy_index_eval (readRegs regs 0 1 none)
      (before.flatten ++ (old ++ rest)) candidate index width
      (before.flatten ++ (old ++ rest))).seq
        (replace_eval (readRegs (readRegs regs 0 1 none) 0 1 none)
          (before.flatten ++ (old ++ rest)) before old candidate rest index width hi hrows ho hc))
  convert h using 1 <;> simp [ sourceCost, hi, readRegs_reset] ; omega

theorem program_trace (regs : Fin 2 → Bool) (before : List (List Bool))
    (old candidate rest index width : List Bool)
    (hi : index.length = before.length)
    (hrows : ∀ row ∈ before, row.length = width.length)
    (ho : old.length = width.length) (hc : candidate.length = width.length) :
    let original := before.flatten ++ (old ++ rest)
    Trace program (sourceCost original.length before.length width.length)
      ((state regs original candidate index width [] []).withPC (some program.entry))
      ((state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) []).withPC none) := by
  dsimp only
  have ht := compiled_halt_trace
    (command_eval regs before old candidate rest index width hi hrows ho hc) 0 8
  have hp : 0 < sourceCost (before.flatten ++ (old ++ rest)).length before.length width.length := by
    simp [sourceCost]
  have htime : sourceCost (before.flatten ++ (old ++ rest)).length
        before.length width.length - 1 + 1 =
      sourceCost (before.flatten ++ (old ++ rest)).length before.length width.length :=
    Nat.sub_add_cancel hp
  rw [htime] at ht
  exact ht

theorem sourceCost_polynomial (D w : ℕ) :
    sourceCost (D * w) D w ≤ 40 * (D + 1) * (w + 1) := by
  unfold sourceCost
  nlinarith

theorem program_primitive (regs : Fin 2 → Bool) (before : List (List Bool))
    (old candidate rest index width : List Bool)
    (hi : index.length = before.length)
    (hrows : ∀ row ∈ before, row.length = width.length)
    (ho : old.length = width.length) (hc : candidate.length = width.length) :
    let original := before.flatten ++ (old ++ rest)
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceCost original.length before.length width.length)
      (primitiveCfg program ((state regs original candidate index width [] []).withPC
        (some program.entry)))
      (primitiveCfg program ((state (readRegs regs 0 1 none) original candidate index width
        (before.flatten ++ (candidate ++ rest)) []).withPC none)) := by
  exact primitive_trace program (program_trace regs before old candidate rest index width hi hrows ho hc)

end SubexponentialSAT.Subexp.CandidateArrayProgram

end OAI.Algorithms
