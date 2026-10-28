import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyExecution
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyLeaves
import OAI.Algorithms.SubexponentialSAT.ExecWorklistLoopBounded
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyStartup

namespace OAI.Algorithms

/-!
# The concrete encoded sparsifier

Only the fixed clause-width parameter controls this program's instruction
table. The input formula and threshold bank remain stack data. The semantic
branch tree is the tree observed from this same program's node executions;
there is no abstract splitter premise in the execution theorem below.

The initial state already contains the normalized pending formula and the
threshold bank. These theorems cover the worklist execution from that state;
normalization and construction of the bank are separate startup phases.
-/

namespace SubexponentialSAT.ExecEncodedSparsifier

open BitProgram StructuredCalls
open ExecCNF (clauseSet formulaSet)
open ExecSparsifyObserved ExecSparsifyBoundary
open ExecSparsifyCanonicalHead
open ExecSparsifyNode (Data)

def program (k : ℕ) :=
  ExecWorklistLoop.Ambient.program (ExecSparsifyProgram.program k) coreReg (coreStack k)

/-- The actual initialized pending stream contains exactly the input formula. -/
noncomputable def initialState {n k : ℕ} (frame : Data k) (F : Formula n) : Data k :=
  ExecWorklistLoop.Ambient.liftData coreReg (coreStack k) frame
    (ExecWorklistLoop.canonicalData encode (ExecSparsifyWorklist.initial F))

/-- The final pending stream is empty and the emitted order is retained. -/
noncomputable def finalState {n k : ℕ} (frame : Data k) (output : List (Formula n)) : Data k :=
  ExecWorklistLoop.Ambient.liftData coreReg (coreStack k) frame
    (ExecWorklistLoop.canonicalData encode ⟨[], output, 0⟩)

noncomputable def runCost {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) : ℕ :=
  ExecWorklistLoop.nodeWork encode (branching frame z hf hb hz)
    (fun G => ExecSparsifyExecution.cost frame z hf hb hz G + 1) F + 6

theorem initial_pending {n k : ℕ} (frame : Data k) (F : Formula n) :
    (initialState frame F).stacks (coreStack k 0) = Encoding.encodeList encode [F] := by
  exact embedState_stack coreReg (coreStack k) frame _ (coreStack_injective k) 0

theorem final_pending {n k : ℕ} (frame : Data k) (output : List (Formula n)) :
    (finalState frame output).stacks (coreStack k 0) = [false] := by
  exact embedState_stack coreReg (coreStack k) frame _ (coreStack_injective k) 0

theorem final_leaves {n k : ℕ} (frame : Data k) (output : List (Formula n)) :
    (finalState frame output).stacks (coreStack k 1) = Encoding.encodeList encode output := by
  exact embedState_stack coreReg (coreStack k) frame _ (coreStack_injective k) 1

theorem final_work_empty {n k : ℕ} (frame : Data k) (output : List (Formula n))
    (i : Fin 5) (hi : 2 ≤ i.val) :
    (finalState frame output).stacks (coreStack k i) = [] := by
  rw [show (finalState frame output).stacks (coreStack k i) =
    (ExecWorklistLoop.canonicalData encode
      (⟨[], output, 0⟩ : ExecSparsifyWorklist.State (Formula n))).stacks i from
    embedState_stack coreReg (coreStack k) frame _ (coreStack_injective k) i]
  fin_cases i <;> simp_all

theorem final_stack_frame {n k : ℕ} (frame : Data k) (output : List (Formula n))
    (i : Fin (k + 39)) (hi : i ∉ Set.range (coreStack k)) :
    (finalState frame output).stacks i = frame.stacks i :=
  embedState_stack_frame coreReg (coreStack k) frame _ i hi

theorem final_registers {n k : ℕ} (frame : Data k) (output : List (Formula n))
    (hf : FrameReady frame) : ∀ i, (finalState frame output).regs i = false := by
  classical
  intro i
  by_cases hi : i ∈ Set.range coreReg
  · obtain ⟨j, rfl⟩ := hi
    exact (embedState_register coreReg (coreStack k) frame _ coreReg_injective j).trans
      (by fin_cases j <;> rfl)
  · exact (embedState_register_frame coreReg (coreStack k) frame _ i hi).trans (hf.1 i)

/-- A complete actual run of the fixed instruction table, to the exact
ordered leaves of its observed branching. The only premises describe the
initialized data and its preserved syntactic invariant. -/
theorem program_runs {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    RunsIn (program k) (runCost frame z hf hb hz F)
      ((initialState frame F).withPC (some (program k).entry))
      ((finalState frame (leaves frame z hf hb hz F)).withPC none) := by
  have hi : ExecSparsifyWorklist.Invariant (Ready k) (ExecSparsifyWorklist.initial F) := by
    simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using hF
  have hr := ExecWorklistLoop.Ambient.run_bounded (ExecSparsifyProgram.program k)
    coreReg (coreStack k) frame coreReg_injective (coreStack_injective k)
    encode (branching frame z hf hb hz) (Ready k)
    (ExecSparsifyExecution.cost frame z hf hb hz)
    (ExecSparsifyExecution.realizes frame z hf hb hz)
    (branching_closed frame z hf hb hz) (ExecSparsifyWorklist.initial F) hi
  simpa only [program, runCost, initialState, finalState, leaves,
    ExecSparsifyWorklist.initial, ExecWorklistLoop.forestWork_cons,
    ExecWorklistLoop.forestWork_nil, Nat.add_zero, ExecWorklistLoop.canonicalData,
    ExecSparsifyWorklist.run_pending_nil] using hr

/-- Simulation of the supplied source configurations. No decoded primitive
leaf-output theorem is asserted here. The complete SAT machine composes the
source program with its consumer before the final compilation. -/
theorem primitive_runs {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F) :
    Computation.RunsIn (primitive (program k)).step
      (primitiveOverhead (program k) * runCost frame z hf hb hz F)
      (primitiveCfg (program k) ((initialState frame F).withPC (some (program k).entry)))
      (primitiveCfg (program k)
        ((finalState frame (leaves frame z hf hb hz F)).withPC none)) :=
  BitProgram.primitive_execution _ (program_runs frame z hf hb hz F hF)

/-- An upper bound on the already-proved concrete node costs yields the
usual visit-factor bound. It is not a premise about a hypothetical splitter. -/
theorem runCost_le_visits {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (B : ℕ) (hB : ∀ G : Formula n, Ready k G →
      ExecSparsifyExecution.cost frame z hf hb hz G +
        ExecWorklistLoop.updateCost encode G ((branching frame z hf hb hz).split G) ≤ B) :
    runCost frame z hf hb hz F ≤ (B + 4) *
      (ExecSparsifyWorklist.run (branching frame z hf hb hz)
        (ExecSparsifyWorklist.initial F)).visits + 6 := by
  have hb' : ∀ G : Formula n, Ready k G →
      (ExecSparsifyExecution.cost frame z hf hb hz G + 1) +
        ExecWorklistLoop.updateCost encode G ((branching frame z hf hb hz).split G) ≤ B + 1 := by
    intro G hG
    have := hB G hG
    omega
  have hn := ExecWorklistLoop.nodeWork_le_visits encode (branching frame z hf hb hz)
    (Ready k) (fun G => ExecSparsifyExecution.cost frame z hf hb hz G + 1) (B + 1)
    (branching_closed frame z hf hb hz) hb' F hF
  simpa only [runCost, ExecSparsifyWorklist.initial_run_visits, Nat.add_assoc] using
    Nat.add_le_add_right hn 6

theorem program_runs_le_visits {n k : ℕ} (frame : Data k) (z : ℕ → ℕ)
    (hf : FrameReady frame) (hb : BankValues z frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ z j) (F : Formula n) (hF : Ready k F)
    (B : ℕ) (hB : ∀ G : Formula n, Ready k G →
      ExecSparsifyExecution.cost frame z hf hb hz G +
        ExecWorklistLoop.updateCost encode G ((branching frame z hf hb hz).split G) ≤ B) :
    RunsIn (program k) ((B + 4) *
      (ExecSparsifyWorklist.run (branching frame z hf hb hz)
        (ExecSparsifyWorklist.initial F)).visits + 6)
      ((initialState frame F).withPC (some (program k).entry))
      ((finalState frame (leaves frame z hf hb hz F)).withPC none) :=
  (program_runs frame z hf hb hz F hF).mono (runCost_le_visits frame z hf hb hz F hF B hB)

/-- Properties attached to the actual ordered output, including its raw
clause/literal normalization and bounded variable occurrences. -/
structure CorrectOutput {n : ℕ} (k B : ℕ) (F : Formula n) (output : List (Formula n)) : Prop where
  models : ∀ a : SAT.Assignment (Fin n),
    SAT.CNF.eval a (formulaSet F) = true ↔
      ∃ G ∈ output, SAT.CNF.eval a (formulaSet G) = true
  satisfiable : SAT.Satisfiable (formulaSet F) ↔
    ∃ G ∈ output, SAT.Satisfiable (formulaSet G)
  clause_nodup : ∀ G ∈ output, (G.map clauseSet).Nodup
  literal_nodup : ∀ G ∈ output, ∀ C ∈ G, C.Nodup
  width : ∀ G ∈ output, SAT.WidthAtMost k (formulaSet G)
  occurrence : ∀ G ∈ output, SAT.OccurrenceAtMost B (formulaSet G)

theorem correct_output {n k : ℕ} (frame : Data k) (M : ℕ)
    (hf : FrameReady frame) (hb : BankValues (SparsificationConstants.z M) frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ SparsificationConstants.z M j)
    (F : Formula n) (hF : Ready k F) (hM : 2 ≤ M) :
    CorrectOutput k (SparsificationConstants.occurrenceCap M k) F
      (leaves frame (SparsificationConstants.z M) hf hb hz F) := by
  constructor
  · exact leaves_models frame _ hf hb hz F
  · exact leaves_satisfiable frame _ hf hb hz F
  · exact leaf_clause_nodup frame _ hf hb hz F hF
  · intro G hG
    exact (leaves_ready frame _ hf hb hz F hF G hG).2.1
  · exact leaf_width frame _ hf hb hz F hF
  · exact leaf_occurrence frame M hf hb hz F hF hM

/-- The complete concrete sparsifier with its SAT, normalization, width, and
occurrence specification. No choice of an abstract branch procedure occurs
in the program or in the hypotheses. -/
theorem program_sparsifies {n k : ℕ} (frame : Data k) (M : ℕ)
    (hf : FrameReady frame) (hb : BankValues (SparsificationConstants.z M) frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ SparsificationConstants.z M j)
    (F : Formula n) (hF : Ready k F) (hM : 2 ≤ M) :
    RunsIn (program k) (runCost frame (SparsificationConstants.z M) hf hb hz F)
      ((initialState frame F).withPC (some (program k).entry))
      ((finalState frame (leaves frame (SparsificationConstants.z M) hf hb hz F)).withPC none) ∧
    CorrectOutput k (SparsificationConstants.occurrenceCap M k) F
      (leaves frame (SparsificationConstants.z M) hf hb hz F) :=
  ⟨program_runs frame _ hf hb hz F hF, correct_output frame M hf hb hz F hF hM⟩

/-- A primitive simulation witness together with the source output's
semantic properties. `CorrectOutput` concerns the source leaf list, not an
independently decoded primitive output. Use `program_sparsifies` to compose
the actual source program into the main machine before compiling once. -/
theorem primitive_sparsifies {n k : ℕ} (frame : Data k) (M : ℕ)
    (hf : FrameReady frame) (hb : BankValues (SparsificationConstants.z M) frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ SparsificationConstants.z M j)
    (F : Formula n) (hF : Ready k F) (hM : 2 ≤ M) :
    Computation.RunsIn (primitive (program k)).step
      (primitiveOverhead (program k) * runCost frame (SparsificationConstants.z M) hf hb hz F)
      (primitiveCfg (program k) ((initialState frame F).withPC (some (program k).entry)))
      (primitiveCfg (program k)
        ((finalState frame (leaves frame (SparsificationConstants.z M) hf hb hz F)).withPC none)) ∧
    CorrectOutput k (SparsificationConstants.occurrenceCap M k) F
      (leaves frame (SparsificationConstants.z M) hf hb hz F) :=
  ⟨primitive_runs frame _ hf hb hz F hF, correct_output frame M hf hb hz F hF hM⟩

/-- Starting from the actual normalizer's ordered output establishes the
input invariant and preserves the original formula's model set. The trace
here begins after normalization and threshold-bank construction. -/
theorem normalized_program_sparsifies {n k : ℕ} (frame : Data k) (M : ℕ)
    (hf : FrameReady frame) (hb : BankValues (SparsificationConstants.z M) frame)
    (hz : ∀ j, 2 ≤ j → j ≤ k → 2 ≤ SparsificationConstants.z M j)
    (F : Formula n) (hF : ExecSunflowerSearch.RawWidthAtMost k F) (hM : 2 ≤ M) :
    RunsIn (program k)
      (runCost frame (SparsificationConstants.z M) hf hb hz
        (ExecSparsifyWorklist.normalizedInput F))
      ((initialState frame (ExecSparsifyWorklist.normalizedInput F)).withPC
        (some (program k).entry))
      ((finalState frame (leaves frame (SparsificationConstants.z M) hf hb hz
        (ExecSparsifyWorklist.normalizedInput F))).withPC none) ∧
    CorrectOutput k (SparsificationConstants.occurrenceCap M k) F
      (leaves frame (SparsificationConstants.z M) hf hb hz
        (ExecSparsifyWorklist.normalizedInput F)) := by
  obtain ⟨ht, hs⟩ := program_sparsifies frame M hf hb hz
    (ExecSparsifyWorklist.normalizedInput F)
    (ExecSparsifyStartup.normalizedInput_ready F k hF) hM
  refine ⟨ht, ?_⟩
  constructor
  · intro a
    simpa only [ExecSparsifyWorklist.normalizedInput_set, SAT.eval_normalize] using hs.models a
  · simpa only [SAT.Satisfiable, ExecSparsifyWorklist.normalizedInput_set,
      SAT.eval_normalize] using hs.satisfiable
  · exact hs.clause_nodup
  · exact hs.literal_nodup
  · exact hs.width
  · exact hs.occurrence

end SubexponentialSAT.ExecEncodedSparsifier

end OAI.Algorithms
