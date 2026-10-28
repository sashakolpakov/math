import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorOuter
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorFrames

namespace OAI.Algorithms

/-! Generic state, padding, and framing calls for the physical Taylor row.
These calls do not depend on the scalar multiplication implementation. -/

namespace SubexponentialSAT.SubexpTaylorRow

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpTaylorControl

def rowState (regs : Fin 8 → Bool) (w : Words) (source count output : List Bool) : State 8 90 :=
  ⟨regs, Fin.addCases (m := 88) (n := 2)
    (SubexpTaylorOuter.outerState regs w source).stacks ![count, output]⟩

@[simp] theorem rowState_inner (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) (i : Fin 88) :
    (rowState regs w source count output).stacks (Fin.castAdd 2 i) =
      (SubexpTaylorOuter.outerState regs w source).stacks i := by
  simp [rowState]

@[simp] theorem rowState_count (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 88 = count := rfl

@[simp] theorem rowState_output (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 89 = output := rfl

@[simp] theorem rowState_77 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 77 = w.stream := rfl
@[simp] theorem rowState_80 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 80 = w.coefficient := rfl
@[simp] theorem rowState_81 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 81 = w.blockWidth := rfl
@[simp] theorem rowState_82 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 82 = w.index := rfl
@[simp] theorem rowState_83 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 83 = w.scratch := rfl
@[simp] theorem rowState_84 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 84 = [] := rfl
@[simp] theorem rowState_85 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 85 = [] := rfl
@[simp] theorem rowState_87 (regs : Fin 8 → Bool) (w : Words)
    (source count output : List Bool) : (rowState regs w source count output).stacks 87 = source := rfl

def shiftPorts : Fin 88 ↪ Fin 90 := ⟨Fin.castAdd 2, Fin.castAdd_injective _ _⟩
def frameRegs : Fin 5 ↪ Fin 8 := ⟨Fin.castAdd 3, Fin.castAdd_injective _ _⟩
def framePorts : Fin 9 ↪ Fin 90 := ⟨![77,81,82,88,80,84,85,83,89], by decide⟩

abbrev frame : Cmd 8 90 :=
  .call (ProgramLinking.liftProgram SubexpTaylorFrames.program frameRegs framePorts)
abbrev clear : Cmd 8 90 := .call (StackRoutines.clearProgram 77 (0 : Fin 8) 1)

theorem embed_shift (regs regs' : Fin 8 → Bool) (w w' : Words)
    (source source' count output : List Bool) :
    embedState id shiftPorts (rowState regs w source count output)
      (SubexpTaylorOuter.outerState regs' w' source') = rowState regs' w' source' count output := by
  apply embedState_eq _ _ Function.injective_id shiftPorts.injective
  · intro i; rfl
  · intro i; simp [shiftPorts]
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i hi
    have hlo : 88 ≤ i.val := by
      by_contra h
      have hil : i.val < 88 := by omega
      exact hi ⟨⟨i.val, hil⟩, by apply Fin.ext; rfl⟩
    have hcases : i = 88 ∨ i = 89 := by
      have hu := i.isLt
      simp only [Fin.ext_iff, Fin.coe_ofNat_eq_mod]
      omega
    rcases hcases with rfl | rfl <;> rfl

noncomputable def mergeRegs (regs : Fin 8 → Bool) (rr : Fin 5 → Bool) : Fin 8 → Bool :=
  Function.extend frameRegs rr regs

theorem embed_frame_input (regs : Fin 8 → Bool) (base : Words)
    (input : List Bool) (N : ℕ) :
    embedState frameRegs framePorts
      (rowState regs (done base input) [] (List.replicate N true) [])
      (SubexpTaylorFrames.state (regs ∘ frameRegs)
        (SubexpTaylorFrames.data base.blockWidth N input [])) =
      rowState regs (done base input) [] (List.replicate N true) [] := by
  apply embedState_eq _ _ frameRegs.injective framePorts.injective
  · intro i; rfl
  · intro i; fin_cases i <;> simp [SubexpTaylorFrames.state, SubexpTaylorFrames.store,
      SubexpTaylorFrames.data, done, framePorts]
  · intros; rfl
  · intros; rfl

theorem embed_frame_output (regs : Fin 8 → Bool) (rr : Fin 5 → Bool) (base : Words)
    (input : List Bool) (N : ℕ) :
    embedState frameRegs framePorts
      (rowState regs (done base input) [] (List.replicate N true) [])
      (SubexpTaylorFrames.state rr
        {SubexpTaylorFrames.data base.blockWidth 0
          (input.drop (N * base.blockWidth.length)) [] with
          output := Encoding.encodeList id (SubexpTaylorFrames.chunks base.blockWidth.length N input)}) =
      rowState (mergeRegs regs rr) (done base (input.drop (N * base.blockWidth.length))) [] []
        (Encoding.encodeList id (SubexpTaylorFrames.chunks base.blockWidth.length N input)) := by
  apply embedState_eq _ _ frameRegs.injective framePorts.injective
  · intro i
    exact frameRegs.injective.extend_apply rr regs i
  · intro i; fin_cases i <;> simp [SubexpTaylorFrames.state, SubexpTaylorFrames.store,
      SubexpTaylorFrames.data, done, framePorts]
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i hi
    revert hi
    refine Fin.addCases (m := 88) (n := 2) ?_ ?_ i
    · intro j hi
      revert hi
      refine Fin.addCases (m := 87) (n := 1) ?_ ?_ j
      · intro k hi
        have hk : k ≠ 77 := by
          intro h
          subst k
          exact hi ⟨0, rfl⟩
        simp [rowState, SubexpTaylorOuter.outerState, done, store, hk]
      · intro k hi; fin_cases k; rfl
    · intro j hi
      fin_cases j
      · exact False.elim (hi ⟨3, rfl⟩)
      · exact False.elim (hi ⟨8, rfl⟩)

theorem frame_eval (regs : Fin 8 → Bool) (base : Words) (input : List Bool) (N : ℕ) :
    ∃ rr, Eval frame (N * (28 * base.blockWidth.length + 33) + 11)
      (rowState regs (done base input) [] (List.replicate N true) [])
      (rowState (mergeRegs regs rr) (done base (input.drop (N * base.blockWidth.length))) [] []
        (Encoding.encodeList id (SubexpTaylorFrames.chunks base.blockWidth.length N input))) := by
  obtain ⟨rr, hr⟩ := SubexpTaylorFrames.program_trace base.blockWidth N input (regs ∘ frameRegs)
  have he := eval_call_lifted SubexpTaylorFrames.program frameRegs framePorts
    (rowState regs (done base input) [] (List.replicate N true) [])
    frameRegs.injective framePorts.injective hr
  exact ⟨rr, by simpa only [frame, embed_frame_input, embed_frame_output] using he⟩

theorem clear_eval (regs : Fin 8 → Bool) (base : Words) (input output : List Bool) :
    Eval clear (2 * input.length + 3)
      (rowState regs (done base input) [] [] output)
      (rowState (readRegs regs 0 1 none) (done base []) [] [] output) := by
  let d := rowState regs (done base input) [] [] output
  have hi : d.stacks 77 = input := rfl
  have hs : StackRoutines.clearStacks 77 d.stacks =
      (rowState (readRegs regs 0 1 none) (done base []) [] [] output).stacks := by
    funext i
    refine Fin.addCases (m := 88) (n := 2) ?_ ?_ i
    · intro j
      refine Fin.addCases (m := 87) (n := 1) ?_ ?_ j
      · intro k
        by_cases hk : k = 77
        · subst k
          rfl
        · have hcast : (Fin.castAdd 2 (Fin.castAdd 1 k) : Fin 90) ≠ 77 := by
            intro h
            apply hk
            apply Fin.ext
            exact congrArg (fun i : Fin 90 => i.val) h
          rw [StackRoutines.clearStacks_frame _ _ _ hcast]
          simp only [d, rowState_inner, SubexpTaylorOuter.outerState_inner]
          simp [store, done, hk]
      · intro k; fin_cases k; rfl
    · intro j; fin_cases j <;> rfl
  have ht := ListRegisterProgram.clear_run (77 : Fin 90) (0 : Fin 8) 1 d.regs d.stacks
  rw [hi, hs] at ht
  exact Eval.call _ ht

end SubexponentialSAT.SubexpTaylorRow

end OAI.Algorithms
