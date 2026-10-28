import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeJobsStage
import OAI.Algorithms.SubexponentialSAT.SubexpCompleteSlotSetup

namespace OAI.Algorithms

/-!
# Constructing the node's retained-slot table from its dimension

The fixed program copies the unary dimension from 109, invokes the actual
dimension-to-slot generator in the relocated job workspace, and moves the
generated width and slot table into 92 and 25. Old destination contents are
physically cleared. Every other stack, including the source and row masters,
is restored exactly.
-/

namespace SubexponentialSAT.SubexpNodeSlotStage

open BitProgram StructuredCalls
open SubexpNodeJobsStage (port port_injective project transfer transferred transfer_eval)
open SubexpSetupStorage (copyCmd copyState copy_eval clearCmd clearState clear_eval)

abbrev Data := State 16 256
abbrev Code := Cmd 16 256

@[simp] theorem port_dimension : port 2 = 140 := rfl
@[simp] theorem port_width : port 3 = 141 := rfl

/-- Only the generator's actual work ports and the copy destination must
start empty. The permanent outputs 92 and 25 may contain old data. -/
structure Ready (d : Data) : Prop where
  dimensionEmpty : d.stacks 140 = []
  temporaryEmpty : d.stacks 139 = []
  widthEmpty : d.stacks 141 = []
  workEmpty : ∀ i ∈ SubexpSlotSetup.work, d.stacks (port i) = []

def generate : Code :=
  .call (ProgramLinking.liftProgram SubexpCompleteSlotSetup.program id port)

theorem generate_eval (D : ℕ) (d : Data)
    (hD : d.stacks 140 = List.replicate D true)
    (h139 : d.stacks 139 = []) (h141 : d.stacks 141 = [])
    (hwork : ∀ i ∈ SubexpSlotSetup.work, d.stacks (port i) = []) :
    ∃ n e, n ≤ SubexpCompleteSlotSetup.bound D ∧ Eval generate n d e ∧
      e.stacks = Function.update
        (Function.update d.stacks 141 (List.replicate (SubexpSymbolicCost.indexBits D) true))
        152 (SubexpSlotSetup.output D) := by
  obtain ⟨e, ⟨n, hn, ht⟩, hs⟩ :=
    SubexpCompleteSlotSetup.program_runs D (project d) hD h139 h141 hwork
  let result := embedState id port d e
  refine ⟨n, result, hn,
    eval_call_from_state _ _ _ _ Function.injective_id port_injective ht, ?_⟩
  funext i
  by_cases hi : ∃ j, port j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [show result.stacks (port j) = e.stacks j from
      embedState_stack id port d e port_injective j, hs]
    change (Function.update
        (Function.update (project d).stacks 3
          (List.replicate (SubexpSymbolicCost.indexBits D) true))
        14 (SubexpSlotSetup.output D)) j =
      (Function.update
        (Function.update d.stacks (port 3)
          (List.replicate (SubexpSymbolicCost.indexBits D) true))
        (port 14) (SubexpSlotSetup.output D)) (port j)
    have h14 : port j = 152 ↔ j = 14 := by
      change port j = port 14 ↔ j = 14
      exact port_injective.eq_iff
    have h3 : port j = 141 ↔ j = 3 := by
      change port j = port 3 ↔ j = 3
      exact port_injective.eq_iff
    simp [Function.update_apply, h14, h3, project, projectState]
  · rw [show result.stacks i = d.stacks i from
      embedState_stack_frame id port d e i hi]
    have h141 : i ≠ 141 := fun h => hi ⟨3, by simpa using h.symm⟩
    have h152 : i ≠ 152 := fun h => hi ⟨14, by simpa using h.symm⟩
    simp [h141, h152]

def move (src dst : Fin 256) : Code :=
  .seq (transfer src 139) (transfer 139 dst)

def moved (src dst : Fin 256) (d : Data) : Data :=
  transferred 139 dst (transferred src 139 d)

theorem move_eval (src dst : Fin 256) (hs : src ≠ 139) (hd : 139 ≠ dst)
    (d : Data) (h139 : d.stacks 139 = []) :
    Eval (move src dst) (6 * (d.stacks src).length + 6) d (moved src dst d) := by
  have h := (transfer_eval src 139 hs d).seq
    (transfer_eval 139 dst hd (transferred src 139 d))
  convert h using 1 <;>
    simp [move, moved, transferred, StackRoutines.transferStacks, h139]
  all_goals omega

theorem moved_stacks (src dst : Fin 256) (hsd : src ≠ dst)
    (hs : src ≠ 139) (hd : 139 ≠ dst)
    (d : Data) (h139 : d.stacks 139 = []) (hout : d.stacks dst = []) :
    (moved src dst d).stacks =
      Function.update (Function.update d.stacks src []) dst (d.stacks src) := by
  funext i
  by_cases hiS : i = src
  · subst i
    simp [moved, transferred, StackRoutines.transferStacks, hs, hsd]
  by_cases hiT : i = 139
  · subst i
    simp [moved, transferred, StackRoutines.transferStacks, hs.symm, hd, h139]
  by_cases hiD : i = dst
  · subst i
    simp [moved, transferred, StackRoutines.transferStacks,
      hd.symm, hsd.symm, h139, hout]
  · simp [moved, transferred, StackRoutines.transferStacks, hiS, hiT, hiD]

def finish : Code := .seq (clearCmd 92) (.seq (clearCmd 25)
  (.seq (move 141 92) (.seq (move 152 25) (clearCmd 140))))

def finished (d : Data) : Data :=
  clearState 140 (moved 152 25 (moved 141 92 (clearState 25 (clearState 92 d))))

def finishCost (d : Data) : ℕ :=
  2 * (d.stacks 92).length + 2 * (d.stacks 25).length +
    6 * (d.stacks 141).length + 6 * (d.stacks 152).length +
    2 * (d.stacks 140).length + 21

theorem finish_eval (d : Data) (h139 : d.stacks 139 = []) :
    Eval finish (finishCost d) d (finished d) := by
  let a := clearState 92 d
  let b := clearState 25 a
  let c := moved 141 92 b
  let e := moved 152 25 c
  have hb139 : b.stacks 139 = [] := by simp [b, a, clearState, h139]
  have hc : c.stacks = Function.update (Function.update b.stacks 141 []) 92 (b.stacks 141) :=
    moved_stacks 141 92 (by decide) (by decide) (by decide) b hb139
      (by simp [b, a, clearState])
  have hc139 : c.stacks 139 = [] := by simp [hc, hb139]
  have he : e.stacks = Function.update (Function.update c.stacks 152 []) 25 (c.stacks 152) :=
    moved_stacks 152 25 (by decide) (by decide) (by decide) c hc139
      (by simp [hc, b, a, clearState])
  have ha25 : a.stacks 25 = d.stacks 25 := by simp [a, clearState]
  have hb141 : b.stacks 141 = d.stacks 141 := by simp [b, a, clearState]
  have hc152 : c.stacks 152 = d.stacks 152 := by simp [hc, b, a, clearState]
  have he140 : e.stacks 140 = d.stacks 140 := by simp [he, hc, b, a, clearState]
  have ht : Eval finish
      ((2 * (d.stacks 92).length + 3) + ((2 * (a.stacks 25).length + 3) +
        ((6 * (b.stacks 141).length + 6) + ((6 * (c.stacks 152).length + 6) +
          (2 * (e.stacks 140).length + 3))))) d (finished d) :=
    (clear_eval 92 d).seq ((clear_eval 25 a).seq
      ((move_eval 141 92 (by decide) (by decide) b hb139).seq
        ((move_eval 152 25 (by decide) (by decide) c hc139).seq (clear_eval 140 e))))
  have htime :
      ((2 * (d.stacks 92).length + 3) + ((2 * (a.stacks 25).length + 3) +
        ((6 * (b.stacks 141).length + 6) + ((6 * (c.stacks 152).length + 6) +
          (2 * (e.stacks 140).length + 3))))) = finishCost d := by
    rw [ha25, hb141, hc152, he140]
    unfold finishCost
    omega
  exact htime ▸ ht

theorem finished_stacks (d : Data) (h139 : d.stacks 139 = []) :
    (finished d).stacks = Function.update
      (Function.update (Function.update
        (Function.update (Function.update d.stacks 92 (d.stacks 141))
          25 (d.stacks 152)) 141 []) 152 []) 140 [] := by
  let b := clearState 25 (clearState 92 d)
  let c := moved 141 92 b
  have hb139 : b.stacks 139 = [] := by simp [b, clearState, h139]
  have hc : c.stacks = Function.update (Function.update b.stacks 141 []) 92 (b.stacks 141) :=
    moved_stacks 141 92 (by decide) (by decide) (by decide) b hb139
      (by simp [b, clearState])
  have hc139 : c.stacks 139 = [] := by simp [hc, hb139]
  have he := moved_stacks 152 25 (by decide) (by decide) (by decide) c hc139
    (by simp [hc, b, clearState])
  change Function.update (moved 152 25 c).stacks 140 [] = _
  rw [he, hc]
  funext i
  by_cases hi140 : i = 140
  · subst i; simp
  by_cases hi141 : i = 141
  · subst i; simp
  by_cases hi152 : i = 152
  · subst i; simp
  by_cases hi92 : i = 92
  · subst i; simp [b, clearState]
  by_cases hi25 : i = 25
  · subst i; simp [b, clearState]
  · simp [b, clearState, hi140, hi141, hi152, hi92, hi25]

def command : Code := .seq (copyCmd 109 140 139) (.seq generate finish)
def program := compiled command 109 25

def bound (D : ℕ) (d : Data) : ℕ :=
  SubexpCompleteSlotSetup.bound D + 9 * D +
    6 * SubexpSymbolicCost.indexBits D + 6 * (SubexpSlotSetup.output D).length +
    2 * (d.stacks 92).length + 2 * (d.stacks 25).length + 27

theorem command_eval (D : ℕ) (d : Data)
    (hD : d.stacks 109 = List.replicate D true) (hready : Ready d) :
    ∃ n e, n + 1 ≤ bound D d ∧ Eval command n d e ∧
      e.stacks = Function.update
        (Function.update d.stacks 92 (List.replicate (SubexpSymbolicCost.indexBits D) true))
        25 (SubexpSlotSetup.output D) := by
  let a := copyState 109 140 d
  have hcopy : Eval (copyCmd 109 140 139) (7 * D + 5) d a := by
    simpa [hD] using copy_eval 109 140 139 d (by decide) (by decide) (by decide)
      hready.temporaryEmpty
  have haD : a.stacks 140 = List.replicate D true := by
    simp [a, SubexpSetupStorage.copyState_stack, hready.dimensionEmpty, hD]
  have ha139 : a.stacks 139 = [] := by
    simp [a, SubexpSetupStorage.copyState_stack, hready.temporaryEmpty]
  have ha141 : a.stacks 141 = [] := by
    simp [a, SubexpSetupStorage.copyState_stack, hready.widthEmpty]
  have hawork : ∀ i ∈ SubexpSlotSetup.work, a.stacks (port i) = [] := by
    intro i hi
    have hi2 : i ≠ 2 := by
      intro heq
      subst i
      exact (by decide : (2 : Fin 128) ∉ SubexpSlotSetup.work) hi
    have hp : port i ≠ 140 := by
      change port i ≠ port 2
      exact port_injective.ne hi2
    simpa [a, SubexpSetupStorage.copyState_stack, hp] using hready.workEmpty i hi
  obtain ⟨n, e, hn, he, hs⟩ := generate_eval D a haD ha139 ha141 hawork
  have he139 : e.stacks 139 = [] := by simp [hs, ha139]
  have h152 : d.stacks 152 = [] := hready.workEmpty 14 (by decide)
  have hfinish : finishCost e =
      2 * (d.stacks 92).length + 2 * (d.stacks 25).length +
        6 * SubexpSymbolicCost.indexBits D + 6 * (SubexpSlotSetup.output D).length +
        2 * D + 21 := by
    simp [finishCost, hs, a, SubexpSetupStorage.copyState_stack, hD,
      hready.dimensionEmpty]
  refine ⟨7 * D + 5 + (n + finishCost e), finished e, ?_,
    hcopy.seq (he.seq (finish_eval e he139)), ?_⟩
  · rw [hfinish]
    unfold bound
    omega
  · rw [finished_stacks e he139, hs]
    funext i
    by_cases hi92 : i = 92
    · subst i; simp
    by_cases hi25 : i = 25
    · subst i; simp
    by_cases hi140 : i = 140
    · subst i; simp [hready.dimensionEmpty]
    by_cases hi141 : i = 141
    · subst i; simp [hready.widthEmpty]
    by_cases hi152 : i = 152
    · subst i; simp [h152]
    · simp [a, SubexpSetupStorage.copyState_stack, hi92, hi25, hi140, hi141, hi152]

theorem program_runs (D : ℕ) (d : Data)
    (hD : d.stacks 109 = List.replicate D true) (hready : Ready d) :
    ∃ e : Data, RunsIn program (bound D d)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update
        (Function.update d.stacks 92 (List.replicate (SubexpSymbolicCost.indexBits D) true))
        25 (SubexpSlotSetup.output D) := by
  obtain ⟨n, e, hn, he, hs⟩ := command_eval D d hD hready
  exact ⟨e, ⟨n + 1, hn, compiled_halt_trace he 109 25⟩, hs⟩

theorem program_primitive (D : ℕ) (d : Data)
    (hD : d.stacks 109 = List.replicate D true) (hready : Ready d) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * bound D d)
      (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (e.withPC none)) ∧
      e.stacks = Function.update
        (Function.update d.stacks 92 (List.replicate (SubexpSymbolicCost.indexBits D) true))
        25 (SubexpSlotSetup.output D) := by
  obtain ⟨e, he, hs⟩ := program_runs D d hD hready
  exact ⟨e, BitProgram.primitive_execution program he, hs⟩

theorem result_frame (D : ℕ) (d e : Data)
    (hs : e.stacks = Function.update
      (Function.update d.stacks 92 (List.replicate (SubexpSymbolicCost.indexBits D) true))
      25 (SubexpSlotSetup.output D))
    (i : Fin 256) (h92 : i ≠ 92) (h25 : i ≠ 25) : e.stacks i = d.stacks i := by
  simp [hs, h92, h25]

end SubexponentialSAT.SubexpNodeSlotStage

end OAI.Algorithms
