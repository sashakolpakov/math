import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputAccess
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Compare the two preserved universal-type byte arrays without changing
the scalar result or any input stack of the matrix-entry service. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryCompare

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 10 46

def registers : Fin 8 → Fin 10 := Fin.castAdd 2
def ports (j : Fin 29) : Fin 46 :=
  if j = 0 then 43 else if j = 28 then 44 else if j = 11 then 45 else j.castAdd 17

theorem registers_injective : Function.Injective registers := Fin.castAdd_injective _ _
theorem ports_injective : Function.Injective ports := by decide

abbrev equality : Cmd 10 46 :=
  liftCommand MatrixInputAccess.equality 0 0 registers ports

theorem equality_eval (a : Data) (h45 : a.stacks 45 = []) :
    ∃ n ≤ 11 * (a.stacks 43).length + 2 * (a.stacks 44).length + 23,
      ∃ out : Fin 10 → Bool,
        Eval equality n a
          ⟨out, Function.update (Function.update a.stacks 43 []) 44 []⟩ ∧
        out 7 = decide (a.stacks 43 = a.stacks 44) := by
  let small := projectState registers ports a
  obtain ⟨n, hn, ht⟩ := MatrixInputAccess.equality_eval small
    (by simpa [small, projectState, ports] using h45)
  let b := embedState registers ports a
    (MatrixInputAccess.compared small (decide (small.stacks 0 = small.stacks 28)))
  have he := eval_liftCommand_from_state MatrixInputAccess.equality 0 0
    registers ports a registers_injective ports_injective ht
  have hbase : Function.extend ports (a.stacks ∘ ports) a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks
      (embedState_project registers ports a registers_injective ports_injective)
  have hs : b.stacks = Function.update (Function.update a.stacks 43 []) 44 [] := by
    change Function.extend ports
      (Function.update (Function.update (a.stacks ∘ ports) 0 []) 28 []) a.stacks = _
    rw [ProgramLinking.extend_update ports_injective,
      ProgramLinking.extend_update ports_injective, hbase]
    rfl
  have hb : b =
      (⟨b.regs, Function.update (Function.update a.stacks 43 []) 44 []⟩ : Data) :=
    congrArg (StructuredProgram.State.mk b.regs) hs
  have hr : b.regs 7 = decide (a.stacks 43 = a.stacks 44) := by
    change b.regs (registers 7) = _
    rw [embedState_register _ _ _ _ registers_injective]
    simp [small, projectState, ports ]
  refine ⟨n + 1, ?_, b.regs, ?_, hr⟩
  · change n ≤ 11 * (a.stacks 43).length + 2 * (a.stacks 44).length + 22 at hn
    omega
  · change Eval equality (n + 1) a b at he
    rw [hb] at he
    exact he

abbrev copy (src dst : Fin 46) : Cmd 10 46 :=
  .call (copyProgram src dst 42 0 1)

def copied (a : Data) (src dst : Fin 46) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

abbrev command : Cmd 10 46 := .seq (copy 23 43) (.seq (copy 24 44) equality)

/-- The comparison is computed from actual copied bytes; every source stack
is restored, including the matrix-entry result on stack 0. -/
theorem command_eval (a : Data)
    (h42 : a.stacks 42 = []) (h43 : a.stacks 43 = [])
    (h44 : a.stacks 44 = []) (h45 : a.stacks 45 = []) :
    ∃ n ≤ 18 * (a.stacks 23).length + 9 * (a.stacks 24).length + 33,
      ∃ out : Fin 10 → Bool,
        Eval command n a ⟨out, a.stacks⟩ ∧
        out 7 = decide (a.stacks 23 = a.stacks 24) := by
  let a1 := copied a 23 43
  let a2 := copied a1 24 44
  have t0 := TupleProgram.copy_eval (23 : Fin 46) 43 42 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) a h42
  have t1 := TupleProgram.copy_eval (24 : Fin 46) 44 42 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) a1
    (by simp [a1, copied, copyStacks, h42])
  obtain ⟨ne, hne, out, te, hout⟩ := equality_eval a2
    (by simp [a2, a1, copied, copyStacks, h45])
  have hf : Function.update (Function.update a2.stacks 43 []) 44 [] = a.stacks := by
    funext j
    by_cases h43j : j = 43
    · subst j; simp [h43]
    by_cases h44j : j = 44
    · subst j; simp [h44]
    simp [a2, a1, copied, copyStacks, h43j, h44j]
  rw [hf] at te
  have he := t0.seq (t1.seq te)
  refine ⟨_, ?_, out, he, ?_⟩
  · simp only [a2, a1, copied, copyStacks, Function.update_self,
      Function.update_of_ne (by decide : (24 : Fin 46) ≠ 43),
      Function.update_of_ne (by decide : (43 : Fin 46) ≠ 44),
      Function.update_of_ne (by decide : (44 : Fin 46) ≠ 43),
      h43, h44, List.append_nil] at hne ⊢
    omega
  · simpa [a2, a1, copied, copyStacks, h43, h44] using hout

def program := compiled command 23 23

theorem program_runsIn (a : Data)
    (h42 : a.stacks 42 = []) (h43 : a.stacks 43 = [])
    (h44 : a.stacks 44 = []) (h45 : a.stacks 45 = []) :
    ∃ out : Fin 10 → Bool,
      RunsIn program (18 * (a.stacks 23).length + 9 * (a.stacks 24).length + 34)
        (a.withPC (some program.entry)) ((⟨out, a.stacks⟩ : Data).withPC none) ∧
      out 7 = decide (a.stacks 23 = a.stacks 24) := by
  obtain ⟨n, hn, out, he, hout⟩ := command_eval a h42 h43 h44 h45
  exact ⟨out, ⟨n + 1, by omega, compiled_halt_trace he 23 23⟩, hout⟩

end SubexponentialSAT.Subexp.ConstraintEntryCompare

end OAI.Algorithms
