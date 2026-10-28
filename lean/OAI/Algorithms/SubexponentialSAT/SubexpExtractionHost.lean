import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExtractionGrid
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! The extraction grid linked into the common sixteen-register,
128-stack host used by the source producer and the outer moment iterator. -/

namespace SubexponentialSAT.SubexpExtractionHost

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 16 128
abbrev Code := StructuredCalls.Cmd 16 128

def registers : Fin 3 → Fin 16 := Fin.castAdd 13
def stackPorts : Fin 24 → Fin 128 := Fin.castAdd 104

theorem registers_injective : Function.Injective registers := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)

theorem stackPorts_injective : Function.Injective stackPorts := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 128 => i.val) h)

def restrict (d : Data) : SubexpExtractionGrid.Data :=
  ⟨fun i => d.regs (registers i), fun i => d.stacks (stackPorts i)⟩

theorem embed_restrict (d : Data) : embedState registers stackPorts d (restrict d) = d := by
  apply embedState_eq_of_ports _ _ _ _ _ registers_injective stackPorts_injective
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl

theorem embed_updated_stacks (d : Data) (inner : SubexpExtractionGrid.Data) (output : List Bool)
    (h : inner.stacks = Function.update (restrict d).stacks 14 output) :
    (embedState registers stackPorts d inner).stacks = Function.update d.stacks 14 output := by
  funext i
  by_cases hi : ∃ j, stackPorts j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [embedState_stack registers stackPorts d inner stackPorts_injective, h]
    by_cases hj : j = 14
    · subst j; simp [stackPorts]
    · have hj' : stackPorts j ≠ 14 := by
        change stackPorts j ≠ stackPorts 14
        exact fun he => hj (stackPorts_injective he)
      simp [Function.update_of_ne hj, Function.update_of_ne hj', restrict]
  · rw [embedState_stack_frame registers stackPorts d inner i hi]
    have hn : i ≠ 14 := by
      intro he
      apply hi
      exact ⟨14, by simpa [stackPorts] using he.symm⟩
    simp [hn]

def gridCall : Code := .call
  (ProgramLinking.liftProgram SubexpExtractionGrid.program registers stackPorts)

/-- Every stack outside the output is preserved by the actual linked grid;
the host's source/record ports above 24 are part of that frame. -/
theorem gridCall_eval (d : Data) (xs source : List Bool) (D width : ℕ)
    (h : SubexpExtractionGrid.Input (restrict d) xs source D width) :
    ∃ ticks e, ticks ≤ SubexpExtractionGrid.gridCost xs source D width + 19 * source.length + 22 ∧
      Eval gridCall ticks d e ∧
      e.stacks = Function.update d.stacks 14
        (UnaryGridProgram.gridOutput (SubexpExtractionGrid.step xs source width)
          D D (d.stacks 14)) ∧
      (∀ i, (¬ ∃ j, registers j = i) → e.regs i = d.regs i) := by
  obtain ⟨ticks, inner, hb, he, hs⟩ :=
    SubexpExtractionGrid.command_eval (restrict d) xs source D width h
  have ht := StructuredCalls.compiled_halt_trace he 0 14
  have hcall := eval_call_lifted SubexpExtractionGrid.program registers stackPorts d
    registers_injective stackPorts_injective ht
  rw [embed_restrict] at hcall
  refine ⟨ticks + 1, embedState registers stackPorts d inner, by omega, hcall, ?_, ?_⟩
  · exact embed_updated_stacks d inner _ hs
  · intro i hi
    exact embedState_register_frame registers stackPorts d inner i hi

theorem gridCall_jobs (d : Data) (xs source : List Bool) (D width : ℕ)
    (old : List SubexpMomentProgram.Job)
    (h : SubexpExtractionGrid.Input (restrict d) xs source D width)
    (hout : d.stacks 14 = SubexpMomentProgram.input old) :
    ∃ ticks e, ticks ≤ SubexpExtractionGrid.gridCost xs source D width + 19 * source.length + 22 ∧
      Eval gridCall ticks d e ∧
      e.stacks = Function.update d.stacks 14
        (SubexpMomentProgram.input ((SubexpExtractionGrid.gridJobs xs source D width D).reverse ++ old)) := by
  obtain ⟨n, e, hn, he, hs, _⟩ := gridCall_eval d xs source D width h
  rw [hout, SubexpExtractionGrid.gridOutput_jobs] at hs
  exact ⟨n, e, hn, he, hs⟩

end SubexponentialSAT.SubexpExtractionHost

end OAI.Algorithms
