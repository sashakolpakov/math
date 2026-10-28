import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpExponentSourceProgram
import OAI.Algorithms.SubexponentialSAT.SubexpOuterJobs
import OAI.Algorithms.SubexponentialSAT.SubexpNodeCacheSetup
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Generate the reusable exponent stream from the stored dimension

The fixed relocation reads unary D directly from 109 and writes the actual
enumerator's result directly to 127. Only an old result at 127 is cleared;
the source cache and all other masters are framed by the execution theorem.
-/

namespace SubexponentialSAT.SubexpNodeExponentMaster

open BitProgram StructuredCalls

abbrev Data := State 16 256

def relocation : Equiv.Perm (Fin 128) :=
  (Equiv.swap 2 109).trans (Equiv.swap 110 127)

def ports (i : Fin 128) : Fin 256 := Fin.castAdd 128 (relocation i)

theorem ports_injective : Function.Injective ports :=
  (Fin.castAdd_injective 128 128).comp relocation.injective

@[simp] theorem ports_dimension : ports 2 = 109 := by decide
@[simp] theorem ports_output : ports 110 = 127 := by decide
@[simp] theorem ports_112 : ports 112 = 112 := by decide
@[simp] theorem ports_113 : ports 113 = 113 := by decide
@[simp] theorem ports_114 : ports 114 = 114 := by decide
@[simp] theorem ports_115 : ports 115 = 115 := by decide
@[simp] theorem ports_116 : ports 116 = 116 := by decide

abbrev call : Cmd 16 256 :=
  .call (ProgramLinking.liftProgram SubexpExponentSourceProgram.program id ports)

abbrev command : Cmd 16 256 := .seq (SubexpNodeCacheSetup.clear 127) call

def work : List (Fin 256) := [112, 113, 114, 115, 116]

def sourceBound (D : ℕ) : ℕ :=
  25 * (3 * D + 2) * (3 * D + 1).choose D + 17 * D + 21

def budget (D : ℕ) (d : Data) : ℕ :=
  2 * (d.stacks 127).length + 3 + sourceBound D

theorem call_eval (d : Data) (D : ℕ)
    (hD : d.stacks 109 = List.replicate D true)
    (h127 : d.stacks 127 = [])
    (hwork : ∀ i ∈ work, d.stacks i = []) :
    ∃ n ≤ sourceBound D, ∃ e : Data, Eval call n d e ∧
      e.stacks = Function.update d.stacks 127 (SubexpExponentSourceProgram.output D) := by
  let projected := projectState id ports d
  have hlocalD : projected.stacks 2 = List.replicate D true := by
    simpa [projected, projectState] using hD
  have hlocalWork : ∀ i ∈ SubexpExponentSourceProgram.work, projected.stacks i = [] := by
    intro i hi
    simp only [SubexpExponentSourceProgram.work, List.mem_cons, List.mem_nil_iff,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [projected, projectState] using h127
    · simpa [projected, projectState] using hwork 112 (by simp [work])
    · simpa [projected, projectState] using hwork 113 (by simp [work])
    · simpa [projected, projectState] using hwork 114 (by simp [work])
    · simpa [projected, projectState] using hwork 115 (by simp [work])
    · simpa [projected, projectState] using hwork 116 (by simp [work])
  obtain ⟨after, ⟨n, hn, ht⟩, hs⟩ :=
    SubexpExponentSourceProgram.program_runs projected D hlocalD hlocalWork
  refine ⟨n, hn, embedState id ports d after, ?_, ?_⟩
  · exact eval_call_from_state _ _ _ _ Function.injective_id ports_injective ht
  · change Function.extend ports after.stacks d.stacks = _
    rw [hs, ProgramLinking.extend_update ports_injective]
    have he := congrArg StructuredProgram.State.stacks
      (embedState_project id ports d Function.injective_id ports_injective)
    change Function.extend ports projected.stacks d.stacks = d.stacks at he
    rw [he, ports_output]

theorem command_eval (d : Data) (D : ℕ)
    (hD : d.stacks 109 = List.replicate D true)
    (hwork : ∀ i ∈ work, d.stacks i = []) :
    ∃ n ≤ budget D d, ∃ e : Data, Eval command n d e ∧
      e.stacks = Function.update d.stacks 127 (SubexpExponentSourceProgram.output D) := by
  let a := SubexpNodeCacheSetup.clearOut d 127
  have hc := SubexpNodeCacheSetup.clear_eval d 127
  obtain ⟨n, hn, e, he, hs⟩ := call_eval a D
    (by simpa [a, SubexpNodeCacheSetup.clearOut] using hD)
    (by simp [a, SubexpNodeCacheSetup.clearOut]) (by
      intro i hi
      have hi127 : i ≠ 127 := by
        simp only [work, List.mem_cons, List.mem_nil_iff, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [a, SubexpNodeCacheSetup.clearOut, hi127] using hwork i hi)
  refine ⟨_, Nat.add_le_add_left hn _, e, hc.seq he, ?_⟩
  simpa [a, SubexpNodeCacheSetup.clearOut] using hs

private theorem encodeList_map_id {A : Type*} (f : A → List Bool) (xs : List A) :
    Encoding.encodeList id (xs.map f) = Encoding.encodeList f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Encoding.encodeList, ih]

theorem output_momentRecords (D : ℕ) :
    SubexpExponentSourceProgram.output D =
      Encoding.encodeList id (SubexpOuterJobs.momentRecords D) := by
  exact (encodeList_map_id _ _).symm

abbrev program : Program 16 256 (size command + 1) := compiled command 109 127

theorem program_runs (d : Data) (D : ℕ)
    (hD : d.stacks 109 = List.replicate D true)
    (hwork : ∀ i ∈ work, d.stacks i = []) :
    ∃ e : Data, RunsIn program (budget D d + 1)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = Function.update d.stacks 127
        (Encoding.encodeList id (SubexpOuterJobs.momentRecords D)) := by
  obtain ⟨n, hn, e, he, hs⟩ := command_eval d D hD hwork
  exact ⟨e, ⟨n + 1, by omega, compiled_halt_trace he 109 127⟩,
    by simpa only [output_momentRecords] using hs⟩

end SubexponentialSAT.SubexpNodeExponentMaster

end OAI.Algorithms
