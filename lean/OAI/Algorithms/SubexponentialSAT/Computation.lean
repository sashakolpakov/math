import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms

/-!
# Measured machine execution for the candidate SAT theorem

The definitions here use the transition semantics of mathlib's finite TM2 machines.
A bound is accompanied by an actual execution certificate; no cost is assigned to
an arbitrary mathematical function. TM2 counts executions of finite statements.
Each fixed statement contains finitely many primitive stack operations.
-/

namespace SubexponentialSAT.Computation

universe u v w

/-- An explicit finite trace of successful transitions. -/
inductive Trace {α : Type u} (step : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace step 0 a a
  | cons {n : ℕ} {a b c : α} :
      step a = some b → Trace step n b c → Trace step (n + 1) a c

/-- A runtime bound means that a transition trace within that bound exists. -/
def RunsIn {α : Type u} (step : α → Option α) (bound : ℕ) (a b : α) : Prop :=
  ∃ n ≤ bound, Trace step n a b

namespace Trace

variable {α : Type u} {step : α → Option α} {n m : ℕ} {a b c : α}

theorem iterate (h : Trace step n a b) :
    (fun s : Option α => s.bind step)^[n] (some a) = some b := by
  induction h with
  | refl => rfl
  | cons hs ht ih =>
      simpa only [Function.iterate_succ_apply, Option.bind_some, hs] using ih

theorem of_iterate
    (h : (fun s : Option α => s.bind step)^[n] (some a) = some b) :
    Trace step n a b := by
  induction n generalizing a with
  | zero =>
      simp only [Function.iterate_zero_apply, Option.some.injEq] at h
      subst b
      exact .refl a
  | succ n ih =>
      cases hs : step a with
      | none =>
          have hn :
              (fun s : Option α => s.bind step)^[n] none = none :=
            Function.iterate_fixed rfl n
          simp only [Function.iterate_succ_apply, Option.bind_some, hs, hn] at h
          cases h
      | some a' =>
          apply Trace.cons hs
          apply ih
          simpa only [Function.iterate_succ_apply, Option.bind_some, hs] using h

theorem trans (h₁ : Trace step n a b) (h₂ : Trace step m b c) :
    Trace step (n + m) a c := by
  apply of_iterate
  rw [Nat.add_comm, Function.iterate_add_apply, h₁.iterate, h₂.iterate]

theorem to_reaches (h : Trace step n a b) : StateTransition.Reaches step a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | cons hs ht ih => exact Relation.ReflTransGen.head hs ih

end Trace

namespace RunsIn

variable {α : Type u} {step : α → Option α} {n m : ℕ} {a b c : α}

theorem refl (step : α → Option α) (a : α) : RunsIn step 0 a a :=
  ⟨0, le_rfl, Trace.refl a⟩

theorem mono (h : RunsIn step n a b) (hn : n ≤ m) : RunsIn step m a b := by
  obtain ⟨t, ht, tr⟩ := h
  exact ⟨t, ht.trans hn, tr⟩

theorem trans (h₁ : RunsIn step n a b) (h₂ : RunsIn step m b c) :
    RunsIn step (n + m) a c := by
  obtain ⟨t₁, ht₁, tr₁⟩ := h₁
  obtain ⟨t₂, ht₂, tr₂⟩ := h₂
  exact ⟨t₁ + t₂, Nat.add_le_add ht₁ ht₂, tr₁.trans tr₂⟩

/-- Our trace bounds are equivalent to mathlib's measured execution certificates. -/
theorem iff_evalsToInTime :
    RunsIn step n a b ↔ Nonempty (StateTransition.EvalsToInTime step a (some b) n) := by
  constructor
  · rintro ⟨t, ht, tr⟩
    exact ⟨{ steps := t, evals_in_steps := tr.iterate, steps_le_m := ht }⟩
  · rintro ⟨h⟩
    exact ⟨h.steps, h.steps_le_m, Trace.of_iterate h.evals_in_steps⟩

/-- A deterministic transition function cannot produce two different terminal results. -/
theorem terminal_unique (h₁ : RunsIn step n a b) (h₂ : RunsIn step m a c)
    (hb : step b = none) (hc : step c = none) : b = c := by
  obtain ⟨_, _, tr₁⟩ := h₁
  obtain ⟨_, _, tr₂⟩ := h₂
  exact Part.mem_unique
    (StateTransition.mem_eval.mpr ⟨tr₁.to_reaches, hb⟩)
    (StateTransition.mem_eval.mpr ⟨tr₂.to_reaches, hc⟩)

end RunsIn

/--
A local simulation obligation: every source transition has an actual target
execution using at most the given overhead target transitions. This is a proposition
about transition functions, not an asserted cost for a source function.
-/
def BoundedSimulation {α : Type u} {β : Type v}
    (source : α → Option α) (target : β → Option β)
    (related : α → β → Prop) (overhead : ℕ) : Prop :=
  ∀ ⦃a a' b⦄, related a b → source a = some a' →
    ∃ b', related a' b' ∧ RunsIn target overhead b b'

/-- Local measured simulations compose over a whole source trace. -/
theorem simulate_trace {α : Type u} {β : Type v}
    {source : α → Option α} {target : β → Option β}
    {related : α → β → Prop} {overhead n : ℕ}
    (sim : BoundedSimulation source target related overhead)
    {a a' : α} (tr : Trace source n a a')
    {b : β} (hrel : related a b) :
    ∃ b', related a' b' ∧ RunsIn target (overhead * n) b b' := by
  induction tr generalizing b with
  | refl a =>
      refine ⟨b, hrel, ?_⟩
      simpa using RunsIn.refl target b
  | @cons n a a' a'' hs ht ih =>
      obtain ⟨b', hb', run₁⟩ := sim hrel hs
      obtain ⟨b'', hb'', run₂⟩ := ih hb'
      refine ⟨b'', hb'', ?_⟩
      simpa [Nat.mul_add, Nat.add_comm] using run₁.trans run₂

/-- The bounded version allows an upper bound on the source trace length. -/
theorem simulate_runsIn {α : Type u} {β : Type v}
    {source : α → Option α} {target : β → Option β}
    {related : α → β → Prop} {overhead n : ℕ}
    (sim : BoundedSimulation source target related overhead)
    {a a' : α} (run : RunsIn source n a a')
    {b : β} (hrel : related a b) :
    ∃ b', related a' b' ∧ RunsIn target (overhead * n) b b' := by
  obtain ⟨t, ht, tr⟩ := run
  obtain ⟨b', hb', run'⟩ := simulate_trace sim tr hrel
  exact ⟨b', hb', run'.mono (Nat.mul_le_mul_left overhead ht)⟩

/-- Two measured refinements compose with the product of their constant overheads. -/
theorem BoundedSimulation.comp {α : Type u} {β : Type v} {γ : Type w}
    {source : α → Option α} {middle : β → Option β} {target : γ → Option γ}
    {related₁ : α → β → Prop} {related₂ : β → γ → Prop} {cost₁ cost₂ : ℕ}
    (sim₁ : BoundedSimulation source middle related₁ cost₁)
    (sim₂ : BoundedSimulation middle target related₂ cost₂) :
    BoundedSimulation source target
      (fun a c => ∃ b, related₁ a b ∧ related₂ b c) (cost₂ * cost₁) := by
  intro a a' c hrelated hstep
  obtain ⟨b, hab, hbc⟩ := hrelated
  obtain ⟨b', ha'b', hrun⟩ := sim₁ hab hstep
  obtain ⟨c', hb'c', hrun'⟩ := simulate_runsIn sim₂ hrun hbc
  exact ⟨c', ⟨b', ha'b', hb'c'⟩, hrun'⟩

/--
A source trace carrying a sum of proposed per-transition costs. This record
alone is not a target-machine runtime proof; that conclusion requires the
measured local simulations in simulate_costedTrace.
-/
inductive CostedTrace {α : Type u} (source : α → Option α) (cost : α → ℕ) :
    ℕ → α → α → Prop
  | refl (a : α) : CostedTrace source cost 0 a a
  | cons {total : ℕ} {a b c : α} :
      source a = some b → CostedTrace source cost total b c →
        CostedTrace source cost (cost a + total) a c

/-- A costed trace still contains genuine source transitions. -/
theorem CostedTrace.exists_trace {α : Type u} {source : α → Option α}
    {cost : α → ℕ} {total : ℕ} {a b : α} (tr : CostedTrace source cost total a b) :
    ∃ steps, Trace source steps a b := by
  induction tr with
  | refl a => exact ⟨0, Trace.refl a⟩
  | cons hs ht ih =>
      obtain ⟨steps, hsteps⟩ := ih
      exact ⟨steps + 1, Trace.cons hs hsteps⟩

/--
State-dependent operation costs give a target runtime bound only when every
source transition is implemented by an actual target trace within that cost.
-/
theorem simulate_costedTrace {α : Type u} {β : Type v}
    {source : α → Option α} {target : β → Option β}
    {related : α → β → Prop} {cost : α → ℕ}
    (sim : ∀ ⦃a a' b⦄, related a b → source a = some a' →
      ∃ b', related a' b' ∧ RunsIn target (cost a) b b')
    {total : ℕ} {a a' : α} (tr : CostedTrace source cost total a a')
    {b : β} (hrel : related a b) :
    ∃ b', related a' b' ∧ RunsIn target total b b' := by
  induction tr generalizing b with
  | refl a => exact ⟨b, hrel, RunsIn.refl target b⟩
  | cons hs ht ih =>
      obtain ⟨b', hb', run₁⟩ := sim hrel hs
      obtain ⟨b'', hb'', run₂⟩ := ih hb'
      exact ⟨b'', hb'', run₁.trans run₂⟩

/--
A finite-control TM2 machine with a binary input/output interface.
We additionally require every work-stack alphabet to be finite.
-/
structure BitMachine extends Turing.TM2ComputableAux Bool Bool where
  finiteAlphabet : ∀ k, Finite (tm.Γ k)

namespace BitMachine

/--
The machine really executes at most the stated number of transitions and halts
with the stated output. The underlying certificate also requires cleared work
stacks and reset finite state, following mathlib's TM2OutputsInTime convention.
-/
def OutputsInTime (machine : BitMachine) (input output : List Bool) (time : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime machine.tm
    (input.map machine.inputAlphabet.symm)
    (some (output.map machine.outputAlphabet.symm)) time)

theorem outputsInTime_mono {machine : BitMachine} {input output : List Bool} {t t' : ℕ}
    (h : machine.OutputsInTime input output t) (ht : t ≤ t') :
    machine.OutputsInTime input output t' := by
  obtain ⟨run⟩ := h
  exact ⟨{ steps := run.steps, evals_in_steps := run.evals_in_steps, steps_le_m := run.steps_le_m.trans ht }⟩

theorem outputsInTime_iff_runsIn (machine : BitMachine)
    (input output : List Bool) (time : ℕ) :
    machine.OutputsInTime input output time ↔
      RunsIn machine.tm.step time
        (Turing.initList machine.tm (input.map machine.inputAlphabet.symm))
        (Turing.haltList machine.tm (output.map machine.outputAlphabet.symm)) := by
  exact RunsIn.iff_evalsToInTime.symm

/-- Successful executions of this deterministic machine have a unique output. -/
theorem outputs_unique {machine : BitMachine} {input output₁ output₂ : List Bool}
    {time₁ time₂ : ℕ}
    (h₁ : machine.OutputsInTime input output₁ time₁)
    (h₂ : machine.OutputsInTime input output₂ time₂) : output₁ = output₂ := by
  have hcfg := RunsIn.terminal_unique
    ((outputsInTime_iff_runsIn machine _ _ _).mp h₁)
    ((outputsInTime_iff_runsIn machine _ _ _).mp h₂) rfl rfl
  have hout := congrArg (fun c : machine.tm.Cfg => c.stk machine.tm.k₁) hcfg
  have hmap : output₁.map machine.outputAlphabet.symm =
      output₂.map machine.outputAlphabet.symm := by
    simpa [Turing.haltList] using hout
  exact (List.map_injective_iff.mpr machine.outputAlphabet.symm.injective) hmap

/-- A concrete binary identity machine, witnessing that the contract is inhabited. -/
def identity : BitMachine where
  tm := Turing.idComputer Bool
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  finiteAlphabet _ := by
    change Finite Bool
    infer_instance

theorem identity_outputs (input : List Bool) : identity.OutputsInTime input input 1 :=
  ⟨{ steps := 1, evals_in_steps := rfl, steps_le_m := le_rfl }⟩

end BitMachine

/--
A primitive multitape bit machine. The finite control first selects one tape.
Its transition table reads only that tape's current bit (or blank), then either
halts with one Boolean answer, moves that tape by one cell, or writes one cell.
There are no statement blocks or unbounded arithmetic primitives.
-/
structure PrimitiveMachine where
  tapeCount : ℕ
  stateCount : ℕ
  inputTape : Fin tapeCount
  start : Fin stateCount
  scan : Fin stateCount → Fin tapeCount
  transition : Fin stateCount → Option Bool →
    Bool ⊕ (Fin stateCount × Turing.TM0.Stmt (Option Bool))

namespace PrimitiveMachine

/-- Tape contents are the only unbounded component of a configuration. -/
structure Cfg (machine : PrimitiveMachine) where
  state : Bool ⊕ Fin machine.stateCount
  tapes : Fin machine.tapeCount → Turing.Tape (Option Bool)

/-- One primitive transition, acting on at most one bit/blank tape cell. -/
def step (machine : PrimitiveMachine) (c : machine.Cfg) : Option machine.Cfg :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    let tapeIndex := machine.scan q
    match machine.transition q (c.tapes tapeIndex).head with
    | .inl answer => some ⟨.inl answer, c.tapes⟩
    | .inr (q', action) =>
      let nextTape :=
        match action with
        | .move direction => (c.tapes tapeIndex).move direction
        | .write symbol => (c.tapes tapeIndex).write symbol
      some ⟨.inr q', Function.update c.tapes tapeIndex nextTape⟩

/-- The actual input word is placed on one tape; every other tape is blank. -/
def init (machine : PrimitiveMachine) (input : List Bool) : machine.Cfg :=
  ⟨.inr machine.start, fun k =>
    if k = machine.inputTape then Turing.Tape.mk₁ (input.map some)
    else Turing.Tape.mk₁ []⟩

/-- A measured execution ending in the specified accepting/rejecting state. -/
def OutputsInTime (machine : PrimitiveMachine) (input : List Bool)
    (answer : Bool) (time : ℕ) : Prop :=
  ∃ c : machine.Cfg, RunsIn machine.step time (machine.init input) c ∧
    c.state = .inl answer

theorem terminal_step {machine : PrimitiveMachine} {c : machine.Cfg} {answer : Bool}
    (h : c.state = .inl answer) : machine.step c = none := by
  simp [step, h]

theorem outputsInTime_mono {machine : PrimitiveMachine} {input : List Bool}
    {answer : Bool} {time time' : ℕ}
    (h : machine.OutputsInTime input answer time) (ht : time ≤ time') :
    machine.OutputsInTime input answer time' := by
  obtain ⟨c, hrun, hanswer⟩ := h
  exact ⟨c, hrun.mono ht, hanswer⟩

theorem outputs_unique {machine : PrimitiveMachine} {input : List Bool}
    {answer₁ answer₂ : Bool} {time₁ time₂ : ℕ}
    (h₁ : machine.OutputsInTime input answer₁ time₁)
    (h₂ : machine.OutputsInTime input answer₂ time₂) : answer₁ = answer₂ := by
  obtain ⟨c₁, hrun₁, ha₁⟩ := h₁
  obtain ⟨c₂, hrun₂, ha₂⟩ := h₂
  have hc := RunsIn.terminal_unique hrun₁ hrun₂
    (terminal_step ha₁) (terminal_step ha₂)
  have ha := congrArg Cfg.state hc
  rw [ha₁, ha₂] at ha
  exact Sum.inl.inj ha

/-- A fully specified finite program returning a fixed bit in one primitive step. -/
def constantMachine (answer : Bool) : PrimitiveMachine where
  tapeCount := 1
  stateCount := 1
  inputTape := 0
  start := 0
  scan _ := 0
  transition _ _ := .inl answer

theorem constantMachine_outputs (answer : Bool) (input : List Bool) :
    (constantMachine answer).OutputsInTime input answer 1 := by
  let c : (constantMachine answer).Cfg :=
    ⟨.inl answer, ((constantMachine answer).init input).tapes⟩
  refine ⟨c, ⟨1, le_rfl, ?_⟩, rfl⟩
  exact Trace.cons rfl (Trace.refl c)

end PrimitiveMachine

/--
A machine simulation must explain actual local transitions and both input/output
representations. An asserted source running time alone cannot supply this record.
-/
structure MachineSimulation (source target : BitMachine) (overhead : ℕ) where
  related : source.tm.Cfg → target.tm.Cfg → Prop
  initial : ∀ input : List Bool,
    related
      (Turing.initList source.tm (input.map source.inputAlphabet.symm))
      (Turing.initList target.tm (input.map target.inputAlphabet.symm))
  transition : BoundedSimulation source.tm.step target.tm.step related overhead
  terminal : ∀ (output : List Bool) (c : target.tm.Cfg),
    related (Turing.haltList source.tm (output.map source.outputAlphabet.symm)) c →
      c = Turing.haltList target.tm (output.map target.outputAlphabet.symm)

/-- Constant-overhead simulation transports measured output certificates. -/
theorem MachineSimulation.outputs {source target : BitMachine} {overhead : ℕ}
    (sim : MachineSimulation source target overhead)
    {input output : List Bool} {time : ℕ}
    (h : source.OutputsInTime input output time) :
    target.OutputsInTime input output (overhead * time) := by
  obtain ⟨c, hrelated, hrun⟩ := simulate_runsIn sim.transition
    ((source.outputsInTime_iff_runsIn _ _ _).mp h) (sim.initial input)
  apply (target.outputsInTime_iff_runsIn _ _ _).mpr
  rwa [sim.terminal output c hrelated] at hrun

/--
The claimed bit-time envelope. The polynomial variable is the length of the
specific explicit encoding, and the exponential variable is the variable count.
-/
noncomputable def runtimeBound (constant : ℝ) (degree : ℕ) (exponent : ℝ)
    (inputBits numVars : ℕ) : ℝ :=
  constant * ((inputBits : ℝ) + 1) ^ degree *
    Real.rpow 2 (exponent * (numVars : ℝ))

theorem runtimeBound_mono_exponent {constant exponent exponent' : ℝ}
    (degree inputBits numVars : ℕ) (hc : 0 ≤ constant)
    (he : exponent ≤ exponent') :
    runtimeBound constant degree exponent inputBits numVars ≤
      runtimeBound constant degree exponent' inputBits numVars := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg numVars)
  · exact mul_nonneg hc (pow_nonneg (by positivity) degree)

/--
Correctness and measured running time for every formula of the specified width.
The output is one bit, and both possible outputs are tied to satisfiability.
The encoder is fixed by SubexponentialSAT.Encoding, rather than existentially chosen.
-/
def MacrostepDecidesWithBound (machine : BitMachine) (width : ℕ)
    (constant : ℝ) (degree : ℕ) (exponent : ℝ) : Prop :=
  ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    ∃ (answer : Bool) (time : ℕ),
      machine.OutputsInTime (Encoding.encodeCNF F) [answer] time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound constant degree exponent
        (Encoding.formulaBitLength F) n

/--
The same exponent is preserved by a proved constant-overhead machine simulation.
The multiplicative constant is charged explicitly.
-/
theorem MachineSimulation.preserves_bound {source target : BitMachine}
    {overhead width degree : ℕ} {constant exponent : ℝ}
    (sim : MachineSimulation source target overhead)
    (h : MacrostepDecidesWithBound source width constant degree exponent) :
    MacrostepDecidesWithBound target width ((overhead : ℝ) * constant) degree exponent := by
  intro n F hF
  obtain ⟨answer, time, hrun, hcorrect, htime⟩ := h n F hF
  refine ⟨answer, overhead * time, sim.outputs hrun, hcorrect, ?_⟩
  calc
    ((overhead * time : ℕ) : ℝ) = (overhead : ℝ) * (time : ℝ) := by simp
    _ ≤ (overhead : ℝ) *
        runtimeBound constant degree exponent (Encoding.formulaBitLength F) n :=
      mul_le_mul_of_nonneg_left htime (Nat.cast_nonneg overhead)
    _ = runtimeBound ((overhead : ℝ) * constant) degree exponent
        (Encoding.formulaBitLength F) n := by
      unfold runtimeBound
      ring

/--
Correctness and complexity on the primitive bit machine, using the fixed
explicit CNF encoding. No macrostep or arithmetic operation is counted as a
single step in this definition.
-/
def DecidesWithBound (machine : PrimitiveMachine) (width : ℕ)
    (constant : ℝ) (degree : ℕ) (exponent : ℝ) : Prop :=
  ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    ∃ (answer : Bool) (time : ℕ),
      machine.OutputsInTime (Encoding.encodeCNF F) answer time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound constant degree exponent
        (Encoding.formulaBitLength F) n

/--
The precise refinement required to turn a finite TM2 block program into a
primitive-bit machine. Every transition needs a measured primitive execution;
the constant overhead cannot be supplied by an unsupported cost annotation.
-/
structure MacroToPrimitiveSimulation (source : BitMachine)
    (target : PrimitiveMachine) (overhead : ℕ) where
  related : source.tm.Cfg → target.Cfg → Prop
  initial : ∀ input : List Bool,
    related
      (Turing.initList source.tm (input.map source.inputAlphabet.symm))
      (target.init input)
  transition : BoundedSimulation source.tm.step target.step related overhead
  terminal : ∀ (answer : Bool) (c : target.Cfg),
    related (Turing.haltList source.tm ([answer].map source.outputAlphabet.symm)) c →
      c.state = .inl answer

/-- A completed low-level refinement transports actual output executions. -/
theorem MacroToPrimitiveSimulation.outputs {source : BitMachine}
    {target : PrimitiveMachine} {overhead : ℕ}
    (sim : MacroToPrimitiveSimulation source target overhead)
    {input : List Bool} {answer : Bool} {time : ℕ}
    (h : source.OutputsInTime input [answer] time) :
    target.OutputsInTime input answer (overhead * time) := by
  obtain ⟨c, hrelated, hrun⟩ := simulate_runsIn sim.transition
    ((source.outputsInTime_iff_runsIn _ _ _).mp h) (sim.initial input)
  exact ⟨c, hrun, sim.terminal answer c hrelated⟩

/-- The primitive-bit bound charges the refinement's constant explicitly. -/
theorem MacroToPrimitiveSimulation.preserves_bound {source : BitMachine}
    {target : PrimitiveMachine} {overhead width degree : ℕ} {constant exponent : ℝ}
    (sim : MacroToPrimitiveSimulation source target overhead)
    (h : MacrostepDecidesWithBound source width constant degree exponent) :
    DecidesWithBound target width ((overhead : ℝ) * constant) degree exponent := by
  intro n F hF
  obtain ⟨answer, time, hrun, hcorrect, htime⟩ := h n F hF
  refine ⟨answer, overhead * time, sim.outputs hrun, hcorrect, ?_⟩
  calc
    ((overhead * time : ℕ) : ℝ) = (overhead : ℝ) * (time : ℝ) := by simp
    _ ≤ (overhead : ℝ) *
        runtimeBound constant degree exponent (Encoding.formulaBitLength F) n :=
      mul_le_mul_of_nonneg_left htime (Nat.cast_nonneg overhead)
    _ = runtimeBound ((overhead : ℝ) * constant) degree exponent
        (Encoding.formulaBitLength F) n := by
      unfold runtimeBound
      ring

/-- The weaker, separately named claim about finite TM2 statement-block steps. -/
def MacrostepExponentFeasible (width : ℕ) (exponent : ℝ) : Prop :=
  ∃ (machine : BitMachine) (constant : ℝ) (degree : ℕ),
    0 < constant ∧ 0 < degree ∧
      MacrostepDecidesWithBound machine width constant degree exponent

/--
The machine, constant, and positive integer polynomial degree are fixed before
the number of variables and the formula vary. This is the exact quantifier
order needed by the candidate's uniform saving.
-/
def ExponentFeasible (width : ℕ) (exponent : ℝ) : Prop :=
  ∃ (machine : PrimitiveMachine) (constant : ℝ) (degree : ℕ),
    0 < constant ∧ 0 < degree ∧
      DecidesWithBound machine width constant degree exponent

/--
A concrete macrostep algorithm yields the primitive-bit target only after a
positive constant-overhead low-level simulation has actually been supplied.
-/
theorem exponentFeasible_of_macro_simulation
    {source : BitMachine} {target : PrimitiveMachine}
    {overhead width degree : ℕ} {constant exponent : ℝ}
    (sim : MacroToPrimitiveSimulation source target overhead)
    (ho : 0 < overhead) (hc : 0 < constant) (hd : 0 < degree)
    (h : MacrostepDecidesWithBound source width constant degree exponent) :
    ExponentFeasible width exponent := by
  refine ⟨target, (overhead : ℝ) * constant, degree, ?_, hd, sim.preserves_bound h⟩
  exact mul_pos (Nat.cast_pos.mpr ho) hc

/-- Increasing the allowed exponential running time preserves feasibility. -/
theorem exponent_mono {width : ℕ} {exponent exponent' : ℝ}
    (he : exponent ≤ exponent') (h : ExponentFeasible width exponent) :
    ExponentFeasible width exponent' := by
  obtain ⟨machine, constant, degree, hc, hd, hdec⟩ := h
  refine ⟨machine, constant, degree, hc, hd, ?_⟩
  intro n F hF
  obtain ⟨answer, time, hrun, hcorrect, htime⟩ := hdec n F hF
  refine ⟨answer, time, hrun, hcorrect, htime.trans ?_⟩
  exact runtimeBound_mono_exponent degree _ _ hc.le he

/-- An algorithm for wider clauses also handles every smaller width. -/
theorem width_antitone {width width' : ℕ} {exponent : ℝ}
    (hw : width ≤ width') (h : ExponentFeasible width' exponent) :
    ExponentFeasible width exponent := by
  obtain ⟨machine, constant, degree, hc, hd, hdec⟩ := h
  refine ⟨machine, constant, degree, hc, hd, ?_⟩
  intro n F hF
  apply hdec n F
  intro clause hclause
  exact (hF clause hclause).trans hw

/--
The candidate theorem as a precise, unproved computational proposition.
There is intentionally no declaration claiming an inhabitant of this proposition.
-/
def CandidateTheorem : Prop :=
  ∀ width : ℕ, 3 ≤ width → ExponentFeasible width (9 / 10 : ℝ)

end SubexponentialSAT.Computation

end OAI.Algorithms
