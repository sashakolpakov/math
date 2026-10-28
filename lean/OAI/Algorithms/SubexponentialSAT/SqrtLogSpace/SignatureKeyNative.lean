import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

/-!
# One full integer signature on the leaf ABI

All port numbers here are leaf-local. The actual key-only machine preserves
the assignment, shifted matrix and every unrelated caller word; it has no
predecessor, countdown, or signature-table input.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

open BitProgram StructuredCalls AttainedSignatureProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def registers : Fin 8 ↪ Fin 40 := Fin.castLEEmb (by decide)

def stackPorts : Fin 16 ↪ Fin 896 where
  toFun i := ⟨if i.val = 0 then 141 else if i.val = 12 then 838 else
    if i.val = 14 then 866 else if i.val = 15 then 847 else 340 + i.val, by
      split_ifs <;> have hi := i.isLt <;> omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have hv := congrArg Fin.val hij
    dsimp at hv
    split_ifs at hv <;> omega

def machine := ProgramLinking.liftProgram AttainedSignatureProgram.program registers stackPorts

def command : Cmd 40 896 := .call machine

structure Ready (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool))) : Prop where
  offset : a.stacks (stackPorts 0) = W
  assignment : a.stacks (stackPorts 12) = bits
  output : a.stacks (stackPorts 14) = []
  matrix : a.stacks (stackPorts 15) = words (rows.map words)
  scratch : ∀ i : Fin 16, i ≠ 0 → i ≠ 12 → i ≠ 14 → i ≠ 15 →
    a.stacks (stackPorts i) = []

theorem Ready.projection {a : State 40 896} {W bits : List Bool}
    {rows : List (List (List Bool))} (ready : Ready a W bits rows) :
    projectState registers stackPorts a = state (a.regs ∘ registers) W bits rows [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change a.stacks (stackPorts i) = _
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h12 : i = 12
  · subst i; exact ready.assignment
  by_cases h14 : i = 14
  · subst i; exact ready.output
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  rw [ready.scratch i h0 h12 h14 h15]
  fin_cases i <;> simp_all

noncomputable def outputState (a : State 40 896) (out : Fin 8 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) : State 40 896 :=
  embedState registers stackPorts a (state out W bits rows (signatureValue W bits rows))

theorem output_stacks (a : State 40 896) (out : Fin 8 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) (ready : Ready a W bits rows) :
    (outputState a out W bits rows).stacks =
      Function.update a.stacks (stackPorts 14) (signatureValue W bits rows) := by
  have hlocal : (state out W bits rows (signatureValue W bits rows)).stacks =
      Function.update (state (a.regs ∘ registers) W bits rows []).stacks 14
        (signatureValue W bits rows) := by
    funext i
    fin_cases i <;> simp [state]
  have hemb : Function.extend stackPorts
      (state (a.regs ∘ registers) W bits rows []).stacks a.stacks = a.stacks := by
    change (embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows [])).stacks = _
    rw [← ready.projection, embedState_project _ _ _ registers.injective stackPorts.injective]
  change Function.extend stackPorts _ a.stacks = _
  rw [hlocal, ProgramLinking.extend_update stackPorts.injective, hemb]

theorem output_register_frame (a : State 40 896) (out : Fin 8 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) (j : Fin 40) (hj : 8 ≤ j.val) :
    (outputState a out W bits rows).regs j = a.regs j := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  dsimp [registers] at hv
  omega

/-- The complete key computation and its all-stack prefix bound concern one
actual run, including its compiled return instruction and all caller words. -/
theorem run (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool))) (ready : Ready a W bits rows)
    (hlen : ∀ row ∈ rows, row.length = bits.length) (frameBound : ℕ)
    (hframe : ∀ i, (a.stacks i).length ≤ frameBound) :
    ∃ n ≤ cost W bits rows + 1, ∃ out,
      Eval command n a (outputState a out W bits rows) ∧
      Trace machine n (a.withPC (some machine.entry))
        ((outputState a out W bits rows).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ n →
        Trace machine prefixSteps (a.withPC (some machine.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          max (16 * (W.length + bits.length + (words (rows.map words)).length) +
            cost W bits rows + 1) frameBound := by
  obtain ⟨n, hn, out, ht⟩ := program_runs (a.regs ∘ registers) W bits rows hlen
  have he := ht
  rw [← ready.projection] at he
  have heval := eval_call_from_state AttainedSignatureProgram.program registers stackPorts a
    registers.injective stackPorts.injective he
  have hi : embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows []) = a := by
    rw [← ready.projection, embedState_project registers stackPorts a registers.injective stackPorts.injective]
  have htrace := ProgramLinking.liftProgram_trace AttainedSignatureProgram.program
    registers stackPorts (a.withPC none) registers.injective stackPorts.injective ht
  have htrace' : Trace machine n (a.withPC (some machine.entry))
      ((outputState a out W bits rows).withPC none) := by
    change Trace machine n
      ((embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows [])).withPC
        (some machine.entry)) ((outputState a out W bits rows).withPC none) at htrace
    rw [hi] at htrace
    exact htrace
  refine ⟨n, hn, out, heval, htrace', ?_⟩
  have hlocal : ∀ prefixSteps intermediate, prefixSteps ≤ n →
      Trace AttainedSignatureProgram.program prefixSteps
        ((state (a.regs ∘ registers) W bits rows []).withPC
          (some AttainedSignatureProgram.program.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤
        16 * (W.length + bits.length + (words (rows.map words)).length) +
          cost W bits rows + 1 := by
    intro prefixSteps intermediate hle hp i
    exact prefix_stack_bound _ _ _ _ _ (hle.trans hn) hp i
  have hb := StructuredSpace.liftProgram_stack_bound AttainedSignatureProgram.program
    registers stackPorts (a.withPC none) registers.injective stackPorts.injective ht hlocal hframe
  change ∀ prefixSteps intermediate, prefixSteps ≤ n →
    Trace machine prefixSteps
      ((embedState registers stackPorts a (state (a.regs ∘ registers) W bits rows [])).withPC
        (some machine.entry)) intermediate → ∀ i, (intermediate.stacks i).length ≤
      max (16 * (W.length + bits.length + (words (rows.map words)).length) +
        cost W bits rows + 1) frameBound at hb
  rw [hi] at hb
  exact hb

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
