import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticSelectorFrame
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticProducerBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-! The actual selected-quartic producer in the Main persistent ABI. -/

namespace SubexponentialSAT.SubexpQuarticSelectorAdapter

open BitProgram StructuredCalls SubexpMainProgram
open SubexpEnumerationPayload SubexpTupleRefinement

abbrev program := SubexpQuarticSelectorControl.program

def selectedBytes (p : ℕ) [Fact p.Prime] : List Bool :=
  encodeTuple (scalarCode p) (QuarticSearch.coefficients p)

@[simp] theorem selectedBytes_length (p : ℕ) [Fact p.Prime] :
    (selectedBytes p).length = 4 * scalarWidth p := by
  simp [selectedBytes, encodeTuple, scalarCode]
  omega

def bound (p inputLength oldLength : ℕ) : ℕ :=
  SubexpQuarticProducer.runtimeBound p inputLength + 7 * inputLength +
    24 * scalarWidth p + 2 * oldLength + 29

theorem bound_le (p inputLength oldLength : ℕ) :
    bound p inputLength oldLength ≤ 16 * inputLength + 2 * oldLength +
      200000 * (p + 1)^6 * (scalarWidth p + 1)^2 + 24 * scalarWidth p + 29 := by
  have h := SubexpQuarticProducerBounds.runtimeBound_le p inputLength
  unfold bound
  omega

/-- The only semantic premise concerns the stored prime. The selected bytes
come from the actual producer trace, including normalization of padded input. -/
theorem program_runs (p : ℕ) [Fact p.Prime] (prime old : List Bool)
    (regs : Fin 14 → Bool) (hprime : BinaryArithmetic.toNat prime = p) :
    RunsIn program (bound p prime.length old.length)
      ((SubexpQuarticSelectorControl.ready regs prime old).withPC (some program.entry))
      ((SubexpQuarticSelectorControl.ready (fun _ => false) prime (selectedBytes p)).withPC none) := by
  obtain ⟨rf, n, hn, ht⟩ := SubexpQuarticProducer.program_runs_toNat p prime
    (SubexpQuarticSelectorControl.producerRegs regs) hprime
  have he := SubexpQuarticSelectorControl.command_eval regs rf prime old (selectedBytes p) n ht
  refine ⟨_, ?_, compiled_halt_trace he 35 36⟩
  simp only [selectedBytes_length]
  unfold bound
  omega

abbrev lowPort := SubexpQuarticSelectorFrame.lowPort
abbrev stackMap := SubexpQuarticSelectorFrame.stackMap
abbrev procedure := SubexpQuarticSelectorFrame.procedure
abbrev WorkspaceReady := @SubexpQuarticSelectorFrame.WorkspaceReady

noncomputable def result {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime] :
    MainState er es := SubexpQuarticSelectorFrame.result a (selectedBytes p)

theorem result_stacks {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : WorkspaceReady a) :
    (result a p).stacks = Function.update a.stacks (persistent es 15) (selectedBytes p) :=
  SubexpQuarticSelectorFrame.result_stacks a (selectedBytes p) ha

theorem result_register {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (i : Fin 14) : (result a p).regs ((procedure er es).registerMap i) = false :=
  SubexpQuarticSelectorFrame.result_register a (selectedBytes p) i

theorem result_register_frame {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (i : Fin (totalRegs er)) (hi : ¬ ∃ j, (procedure er es).registerMap j = i) :
    (result a p).regs i = a.regs i :=
  SubexpQuarticSelectorFrame.result_register_frame a (selectedBytes p) i hi

theorem result_control {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (i : Fin 3) : (result a p).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  SubexpQuarticSelectorFrame.result_control a (selectedBytes p) i

theorem result_selected {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : WorkspaceReady a) :
    (result a p).stacks (persistent es 15) = selectedBytes p := by
  rw [result_stacks a p ha]
  simp

theorem result_prime {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : WorkspaceReady a) :
    (result a p).stacks (persistent es 6) = a.stacks (persistent es 6) := by
  rw [result_stacks a p ha]
  simp [(persistent_injective es).eq_iff]

theorem result_workspace {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : WorkspaceReady a) : WorkspaceReady (result a p) := by
  intro i
  rw [result_stacks a p ha,
    Function.update_of_ne (SubexpQuarticSelectorFrame.low_ne_persistent es i 15)]
  exact ha i

/-- Full actual execution from the retained prime to newly selected bytes.
The old coefficient word may be arbitrary and its erasure is charged. -/
theorem execution {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : WorkspaceReady a)
    (hprime : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p) :
    ∃ n, n ≤ bound p (a.stacks (persistent es 6)).length (a.stacks (persistent es 15)).length ∧
      Eval (procedure er es).invoke n a (result a p) := by
  obtain ⟨n, hn, ht⟩ := program_runs p (a.stacks (persistent es 6))
    (a.stacks (persistent es 15)) (a.regs ∘ (procedure er es).registerMap) hprime
  rw [← SubexpQuarticSelectorFrame.project_ready a ha] at ht
  exact ⟨n, hn, Procedure.invoke_trace (procedure er es) a _ ht⟩

def mainProgram (er es : ℕ) := ProgramLinking.liftProgram (procedure er es).program
  (procedure er es).registerMap (procedure er es).stack

theorem main_runsIn {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : WorkspaceReady a)
    (hprime : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p) :
    RunsIn (mainProgram er es)
      (bound p (a.stacks (persistent es 6)).length (a.stacks (persistent es 15)).length)
      (a.withPC (some (mainProgram er es).entry)) ((result a p).withPC none) := by
  obtain ⟨n, hn, he⟩ := execution a p ha hprime
  refine ⟨n, hn, ?_⟩
  cases he with
  | call _ ht => exact ht

theorem main_primitive {er es : ℕ} (a : MainState er es) (p : ℕ) [Fact p.Prime]
    (ha : WorkspaceReady a)
    (hprime : BinaryArithmetic.toNat (a.stacks (persistent es 6)) = p) :
    Computation.RunsIn (primitive (mainProgram er es)).step
      (primitiveOverhead (mainProgram er es) *
        bound p (a.stacks (persistent es 6)).length (a.stacks (persistent es 15)).length)
      (primitiveCfg (mainProgram er es) (a.withPC (some (mainProgram er es).entry)))
      (primitiveCfg (mainProgram er es) ((result a p).withPC none)) :=
  BitProgram.primitive_execution _ (main_runsIn a p ha hprime)

end SubexponentialSAT.SubexpQuarticSelectorAdapter

end OAI.Algorithms
