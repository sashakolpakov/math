import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeLocalSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexMaster
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWideLoop
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! One physical setup program for the widened node host. -/

namespace SubexponentialSAT.SubexpNodeWideSetup

open BitProgram StructuredCalls

abbrev Data := State 16 352

def lowPorts : Fin 256 → Fin 352 := Fin.castAdd 96
theorem lowPorts_injective : Function.Injective lowPorts := Fin.castAdd_injective _ _

/-- The old external range skips the new protected static-data bank. -/
def oldPorts (i : Fin 320) : Fin 352 :=
  if h : i.val < 256 then ⟨i.val, by omega⟩ else ⟨i.val + 32, by omega⟩

theorem oldPorts_injective : Function.Injective oldPorts := by
  intro i j h
  by_cases hi : i.val < 256 <;> by_cases hj : j.val < 256
  all_goals
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp [oldPorts, hi, hj] at hv
    omega

def lowState (d : Data) : State 16 256 := projectState id lowPorts d
def oldState (d : Data) : State 16 320 := projectState id oldPorts d

abbrev localCall : Cmd 16 352 :=
  .call (ProgramLinking.liftProgram SubexpNodeLocalSetup.program id lowPorts)

abbrev indexCall : Cmd 16 352 :=
  .call (ProgramLinking.liftProgram SubexpNodeIndexMaster.program id oldPorts)

abbrev command : Cmd 16 352 := .seq localCall indexCall

def localResult (d : Data) (D : ℕ) : Fin 352 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update d.stacks 92 (List.replicate (SubexpSymbolicCost.indexBits D) true))
      127 (Encoding.encodeList id (SubexpOuterJobs.momentRecords D)))
        122 [false]) 123 (SubexpScalarLiteralProgram.rawLiteral D (d.stacks 120)))
          124 (SubexpLiftRing.fixedBits (d.stacks 10).length 1)

def resultStacks (d : Data) (D : ℕ) : Fin 352 → List Bool :=
  Function.update (localResult d D) 125 (d.stacks 332)

def localBudget (d : Data) (D : ℕ) : ℕ := SubexpNodeLocalSetup.budget (lowState d) D + 1
def indexCost (d : Data) : ℕ := 2 * (d.stacks 125).length + 7 * (d.stacks 332).length + 9
def budget (d : Data) (D : ℕ) : ℕ := localBudget d D + indexCost d

structure Ready (d : Data) (D : ℕ) : Prop where
  dimension : d.stacks 109 = List.replicate D true
  empty0 : d.stacks 0 = []
  empty1 : d.stacks 1 = []
  empty4 : d.stacks 4 = []
  exponent : ∀ i ∈ SubexpNodeExponentMaster.work, (lowState d).stacks i = []
  literal : SubexpNodeRawConstants.WorkEmpty (lowState d)
  zero : d.stacks 122 = []
  one : d.stacks 123 = []
  scalar : d.stacks 124 = []
  width : 0 < (d.stacks 10).length
  temporary : d.stacks 337 = []

theorem localCall_eval (d : Data) (D : ℕ) (hr : Ready d D) :
    ∃ n ≤ localBudget d D, ∃ e : Data, Eval localCall n d e ∧
      e.stacks = localResult d D := by
  obtain ⟨out, ⟨n, hn, ht⟩, hs⟩ := SubexpNodeLocalSetup.program_runs (lowState d) D
    hr.dimension hr.empty0 hr.empty1 hr.empty4 hr.exponent hr.literal
    hr.zero hr.one hr.scalar hr.width
  refine ⟨n, hn, embedState id lowPorts d out,
    eval_call_from_state _ _ _ _ Function.injective_id lowPorts_injective ht, ?_⟩
  change Function.extend lowPorts out.stacks d.stacks = _
  rw [hs]
  unfold SubexpNodeLocalSetup.resultStacks
  rw [ProgramLinking.extend_update lowPorts_injective,
    ProgramLinking.extend_update lowPorts_injective,
    ProgramLinking.extend_update lowPorts_injective,
    ProgramLinking.extend_update lowPorts_injective,
    ProgramLinking.extend_update lowPorts_injective]
  have hf := congrArg StructuredProgram.State.stacks
    (embedState_project id lowPorts d Function.injective_id lowPorts_injective)
  change Function.extend lowPorts (lowState d).stacks d.stacks = d.stacks at hf
  rw [hf]
  rfl

theorem indexCall_eval (d : Data) (htmp : d.stacks 337 = []) :
    ∃ e : Data, Eval indexCall (indexCost d) d e ∧
      e.stacks = Function.update d.stacks 125 (d.stacks 332) := by
  have ht := SubexpNodeIndexMaster.program_trace (oldState d) htmp
  let e := embedState id oldPorts d (SubexpNodeIndexMaster.result (oldState d))
  refine ⟨e, ?_, ?_⟩
  · have he := eval_call_from_state _ _ _ _ Function.injective_id oldPorts_injective ht
    convert he using 1
    simp [indexCost, SubexpNodeIndexMaster.cost, oldState, projectState, oldPorts]
  · change Function.extend oldPorts
      (Function.update (oldState d).stacks 125 ((oldState d).stacks 300)) d.stacks = _
    rw [ProgramLinking.extend_update oldPorts_injective]
    have hf := congrArg StructuredProgram.State.stacks
      (embedState_project id oldPorts d Function.injective_id oldPorts_injective)
    change Function.extend oldPorts (oldState d).stacks d.stacks = d.stacks at hf
    rw [hf]
    rfl

theorem command_eval (d : Data) (D : ℕ) (hr : Ready d D) :
    ∃ n ≤ budget d D, ∃ e : Data, Eval command n d e ∧
      e.stacks = resultStacks d D := by
  obtain ⟨n, hn, a, ha, hs⟩ := localCall_eval d D hr
  obtain ⟨e, he, ht⟩ := indexCall_eval a (by simpa [hs, localResult] using hr.temporary)
  have hc : indexCost a = indexCost d := by simp [indexCost, hs, localResult]
  refine ⟨n + indexCost a, ?_, e, ha.seq he, ?_⟩
  · simpa only [budget, hc] using Nat.add_le_add_right hn (indexCost d)
  · simpa [resultStacks, hs, localResult] using ht

abbrev program : Program 16 352 (size command + 1) := compiled command 332 125

theorem program_runs (d : Data) (D : ℕ) (hr : Ready d D) :
    ∃ e : Data, RunsIn program (budget d D + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧ e.stacks = resultStacks d D := by
  obtain ⟨n, hn, e, he, hs⟩ := command_eval d D hr
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 332 125⟩, hs⟩

theorem result_static (d : Data) (D : ℕ) (i : Fin 32) :
    resultStacks d D (SubexpNodeWideLoop.localPorts (SubexpNodeWideLoop.staticPorts i)) =
      d.stacks (SubexpNodeWideLoop.localPorts (SubexpNodeWideLoop.staticPorts i)) := by
  let k := SubexpNodeWideLoop.localPorts (SubexpNodeWideLoop.staticPorts i)
  have hk : 256 ≤ k.val := by
    simp [k, SubexpNodeWideLoop.localPorts, SubexpNodeWideLoop.staticPorts]
  have hn (j : Fin 352) (hj : j.val < 256) : k ≠ j := by
    intro h
    rw [h] at hk
    omega
  change resultStacks d D k = d.stacks k
  simp [resultStacks, localResult, hn 92 (by decide), hn 122 (by decide),
    hn 123 (by decide), hn 124 (by decide), hn 125 (by decide), hn 127 (by decide)]

end SubexponentialSAT.SubexpNodeWideSetup

end OAI.Algorithms
