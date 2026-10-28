import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramRefinement

namespace OAI.Algorithms

/-! The concrete native sparse-hash controller, including alphabet expansion,
unary control construction and candidate generation.  The remaining service
contract is an actual bit-machine evaluation of each candidate's mass; it is
not an arithmetic oracle or a unit-cost semantic callback. -/

namespace SubexponentialSAT.SqrtLog.Execution.Hash

open BitProgram StructuredCalls HashSelectProgram

structure Ports (R S : ℕ) where
  register : Fin 10 → Fin R
  stack : Fin 14 → Fin S
  register_injective : Function.Injective register
  stack_injective : Function.Injective stack

abbrev Ports.controller {R S : ℕ} (p : Ports R S) : ControllerPorts R S :=
  relocateController p.register p.stack p.register_injective p.stack_injective

def ContextFrame {R S : ℕ} (p : Ports R S) (before after : State R S) : Prop :=
  (∀ i, (∀ j, p.stack j ≠ i) → after.stacks i = before.stacks i) ∧
  (∀ i, (∀ j, p.register j ≠ i) → after.regs i = before.regs i)

abbrev command {R S : ℕ} (p : Ports R S) (mass : Cmd R S) : Cmd R S :=
  .seq (HashSetup.generate p.register p.stack) (controller p.controller mass)

abbrev program {R S : ℕ} (p : Ports R S) (mass : Cmd R S) :=
  compiled (command p mass) (p.stack 0) (p.stack 9)

def budget (count depth rounds : List Bool) (B C cost : ℕ) : ℕ :=
  HashSetup.budget count depth rounds + 1 +
    controllerBudget B C cost
      (candidateEncoding (generatedPayloads (SubexpAlphabetProgram.alphabetWords count)
        (CounterPrograms.value depth))).length
      (generatedPayloads (SubexpAlphabetProgram.alphabetWords count)
        (CounterPrograms.value depth)).length (CounterPrograms.value rounds)

/-- All hypotheses about mass concern physical executions on reachable-size
matrices. The context frame only contains registers/stacks outside the fixed
setup layout, so a formula and ring context remain available to the service. -/
theorem command_eval {R S : ℕ} (p : Ports R S) (mass : Cmd R S)
    (a : State R S) (initial : Records) (score : Records → List Bool → List Bool)
    (valid : Records → List Bool → Prop) (B C cost : ℕ)
    (seed : List Bool) (rest : Records)
    (ready : HashInputs.Ready (projectState p.register p.stack a))
    (rows : a.stacks (p.stack 9) = candidateEncoding initial)
    (family : generatedPayloads
      (SubexpAlphabetProgram.alphabetWords (a.stacks (p.stack 0)))
      (CounterPrograms.value (a.stacks (p.stack 5))) = seed :: rest)
    (hmass : ∀ frame, ContextFrame p a frame → ∀ rows' state,
      rows'.length < initial.length + CounterPrograms.value (a.stacks (p.stack 6)) →
      rows' ⊆ (seed :: rest) ++ initial →
      ControllerReady p.controller frame (seed :: rest) rows' state →
      MassSpec mass p.controller.trial.core (afterCopyFamily p.controller.trial state)
        (score rows') (valid rows') B C cost)
    (hp : ∀ rows',
      rows'.length < initial.length + CounterPrograms.value (a.stacks (p.stack 6)) →
      rows' ⊆ (seed :: rest) ++ initial → ∀ bits ∈ seed :: rest,
        valid rows' bits ∧ bits.length ≤ C ∧ (score rows' bits).length = B) :
    ∃ t ≤ budget (a.stacks (p.stack 0)) (a.stacks (p.stack 5)) (a.stacks (p.stack 6)) B C cost,
      ∃ b : State R S, Eval (command p mass) t a b ∧
        b.stacks (p.stack 9) = candidateEncoding
          (iter (payloadNext score seed rest) (CounterPrograms.value (a.stacks (p.stack 6))) initial) ∧
        b.stacks (p.stack 13) = [] := by
  obtain ⟨t1, ht1, prepared, hprepare, hready, hrounds, hstacks, hregs⟩ :=
    HashSetup.generate_eval p.register p.stack p.register_injective p.stack_injective
      initial a ready rows
  rw [family] at hready
  let rounds := List.replicate (CounterPrograms.value (a.stacks (p.stack 6))) true
  have hmass' : ∀ rows' state, rows'.length < initial.length + rounds.length →
      rows' ⊆ (seed :: rest) ++ initial →
      ControllerReady p.controller prepared (seed :: rest) rows' state →
      MassSpec mass p.controller.trial.core (afterCopyFamily p.controller.trial state)
        (score rows') (valid rows') B C cost := by
    simpa only [rounds, List.length_replicate] using hmass prepared ⟨hstacks, hregs⟩
  have hp' : ∀ rows', rows'.length < initial.length + rounds.length →
      rows' ⊆ (seed :: rest) ++ initial → ∀ bits ∈ seed :: rest,
        valid rows' bits ∧ bits.length ≤ C ∧ (score rows' bits).length = B := by
    simpa only [rounds, List.length_replicate] using hp
  obtain ⟨t2, ht2, b, hb, hk, _, he⟩ := controller_eval_bounded p.controller mass
    prepared score valid B C cost seed rest initial rounds prepared hmass' hp' hready hrounds
  refine ⟨t1+t2, ?_, b, hprepare.seq he, ?_, hk⟩
  · simp only [rounds, List.length_replicate] at ht2
    dsimp only [budget]
    rw [family, List.length_cons]
    omega
  · simpa only [rounds, List.length_replicate, Ports.controller,
      relocateController] using hb.2.2.1

/-- The decoded returned matrix is exactly the semantic greedy run whenever
the paid mass service's bit scores have their specified numeric values. This
decoding is a correctness statement, not a free machine operation. -/
theorem decoded_result {V : Type*} (evaluate : List V → ℕ) (decode : List Bool → V)
    (score : Records → List Bool → List Bool) (seed : List Bool) (rest initial : Records)
    (K : ℕ)
    (hs : ∀ t < K, ∀ bits ∈ seed :: rest,
      BinaryArithmetic.toNat (score (iter (payloadNext score seed rest) t initial) bits) =
        evaluate (decode bits :: (iter (payloadNext score seed rest) t initial).map decode)) :
    (iter (payloadNext score seed rest) K initial).map decode =
      HashSelect.listRun evaluate decode seed rest (initial.map decode) K :=
  iter_decode evaluate decode score seed rest initial K hs

/-- Any proved execution of the complete command compiles to the same fixed
primitive machine. In particular, no varying alphabet size, P or K enters
the instruction table. -/
theorem primitive_run {R S : ℕ} (p : Ports R S) (mass : Cmd R S)
    {a b : State R S} {t : ℕ} (h : Eval (command p mass) t a b) :
    Computation.RunsIn (primitive (program p mass)).step
      (primitiveOverhead (program p mass) * (t+1))
      (primitiveCfg (program p mass) (a.withPC (some (program p mass).entry)))
      (primitiveCfg (program p mass) (b.withPC none)) := by
  exact primitive_execution (program p mass)
    ⟨t+1, le_rfl, compiled_halt_trace h (p.stack 0) (p.stack 9)⟩

end SubexponentialSAT.SqrtLog.Execution.Hash

end OAI.Algorithms
