import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StackMachine

namespace OAI.Algorithms

/-!
A global finite controller for one-head finite stack programs. A source step
first inspects one finite-alphabet stack top, then changes finite control and
keeps, pops, or pushes that stack. The compiled controller performs only the
primitive bit reads, moves, and writes of StackMachine.controlStep.
-/

namespace SubexponentialSAT.StackCompiler

open Turing SubexponentialSAT.Computation SubexponentialSAT.StackMachine SubexponentialSAT.StackEncoding

inductive Mutation (α : Type) where
  | keep
  | pop
  | push (value : α)
  deriving Fintype

def Mutation.apply {α : Type} : Mutation α → List α → List α
  | .keep, s => s
  | .pop, s => s.tail
  | .push a, s => a :: s

def mutationActions {α : Type} (code : BlockCode α) : Mutation α → List Action
  | .keep => []
  | .pop => popBits code.width
  | .push a => pushBits (code.block a)

theorem mutationActions_length {α : Type} (code : BlockCode α) (op : Mutation α) :
    (mutationActions code op).length ≤ 2 * code.width := by
  cases op <;> simp [mutationActions, code.length_block]

theorem mutationActions_correct {α : Type} (code : BlockCode α)
    (op : Mutation α) (stack : List α) :
    execute (mutationActions code op) (dataTape (encodeDataStack code stack)) =
      dataTape (encodeDataStack code (op.apply stack)) := by
  cases op with
  | keep => rfl
  | pop =>
      simpa [mutationActions, Mutation.apply, drop_width_eq_tail] using
        execute_popBits_drop code.width (encodeDataStack code stack)
  | push a =>
      simpa [mutationActions, Mutation.apply, encodeDataStack_cons] using
        execute_pushBits (code.block a) (encodeDataStack code stack)

structure StackProgram (Q : Type) {t : ℕ} (Γ : Fin t → Type) where
  inputTape : Fin t
  start : Q
  select : Q → Fin t
  transition : (q : Q) → Option (Γ (select q)) →
    Bool ⊕ (Q × Mutation (Γ (select q)))

structure StackCfg (Q : Type) {t : ℕ} (Γ : Fin t → Type) where
  state : Bool ⊕ Q
  stk : ∀ k, List (Γ k)

def stackStep {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (c : StackCfg Q Γ) : Option (StackCfg Q Γ) :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    match p.transition q (c.stk (p.select q)).head? with
    | .inl answer => some ⟨.inl answer, c.stk⟩
    | .inr (q', op) => some ⟨.inr q',
        Function.update c.stk (p.select q) (op.apply (c.stk (p.select q)))⟩

/-- The source input stack uses its given Boolean interface; all other stacks are empty. -/
def initialCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (inputAlphabet : Γ p.inputTape ≃ Bool)
    (input : List Bool) : StackCfg Q Γ :=
  ⟨.inr p.start, Function.update (fun _ => []) p.inputTape
    (input.map inputAlphabet.symm)⟩

abbrev CodeFamily {t : ℕ} (Γ : Fin t → Type) := ∀ k, BlockCode (Γ k)

abbrev State {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) :=
  Q ⊕ (((q : Q) × ReaderState (codes (p.select q)).width) ⊕
    ((k : Fin t) × (Q × Mutation (Γ k) × Fin (2 * (codes k).width + 1))))

def ready {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ} (q : Q) : State p codes := .inl q

def reading {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ}
    (q : Q) (r : ReaderState (codes (p.select q)).width) : State p codes :=
  .inr (.inl ⟨q, r⟩)

def acting {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    {p : StackProgram Q Γ} {codes : CodeFamily Γ}
    (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (i : Fin (2 * (codes k).width + 1)) : State p codes :=
  .inr (.inr ⟨k, q, op, i⟩)

def controller {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (decode : ∀ k, List Bool → Option (Γ k)) : Controller (State p codes) t where
  inputTape := p.inputTape
  start := ready p.start
  scan
    | .inl q => p.select q
    | .inr (.inl ⟨q, _⟩) => p.select q
    | .inr (.inr ⟨k, _⟩) => k
  transition
    | .inl q, bit => .inr (reading q (0, fun _ => none), .write bit)
    | .inr (.inl ⟨q, r⟩), bit =>
      let width := (codes (p.select q)).width
      if h : r.1.val < width then
        .inr (reading q (⟨r.1.val + 1, by omega⟩,
          Function.update r.2 ⟨r.1.val, h⟩ bit), .move .right)
      else if h' : r.1.val < 2 * width then
        .inr (reading q (⟨r.1.val + 1, by omega⟩, r.2), .move .left)
      else
        match p.transition q (decode (p.select q) (registerBits r.2)) with
        | .inl answer => .inl answer
        | .inr (q', op) => .inr (acting (p.select q) q' op 0, .write bit)
    | .inr (.inr ⟨k, q, op, i⟩), bit =>
      let actions := mutationActions (codes k) op
      if h : i.val < actions.length then
        .inr (acting k q op ⟨i.val + 1,
          Nat.lt_succ_of_le (Nat.le_trans (Nat.succ_le_of_lt h)
            (mutationActions_length (codes k) op))⟩, actions[i.val])
      else .inr (ready q, .write bit)

def tapeEncoding {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (codes : CodeFamily Γ) (c : StackCfg Q Γ) : Fin t → BitTape :=
  fun k => dataTape (encodeDataStack (codes k) (c.stk k))

def encodeCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) (c : StackCfg Q Γ) :
    ControlCfg (State p codes) t :=
  ⟨c.state.map id ready, tapeEncoding codes c⟩

def readCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (q : Q) (base : Fin t → BitTape)
    (r : ReaderState (codes (p.select q)).width) (tape : BitTape) :
    ControlCfg (State p codes) t :=
  ⟨.inr (reading q r), Function.update base (p.select q) tape⟩

def actionCfg {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ)
    (k : Fin t) (q : Q) (op : Mutation (Γ k)) (base : Fin t → BitTape)
    (i : Fin ((mutationActions (codes k) op).length + 1)) (tape : BitTape) :
    ControlCfg (State p codes) t :=
  ⟨.inr (acting k q op ⟨i.val,
      lt_of_lt_of_le i.isLt (Nat.succ_le_succ (mutationActions_length (codes k) op))⟩),
    Function.update base k tape⟩

section Fragments

variable {Q : Type} {t : ℕ} {Γ : Fin t → Type}
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

theorem reader_scan_table (q : Q) (base : Fin t → BitTape)
    (i : ℕ) (hi : i < (codes (p.select q)).width)
    (r : Registers (codes (p.select q)).width) (tape : BitTape) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨i, by omega⟩, r) tape) =
    some (readCfg p codes q base
      (⟨i + 1, by omega⟩, Function.update r ⟨i, hi⟩ tape.head) (tape.move .right)) := by
  simp [controlStep, controller, readCfg, reading, hi, applyAction,
    Function.update_idem]

theorem reader_back_table (q : Q) (base : Fin t → BitTape)
    (i : ℕ) (hlo : (codes (p.select q)).width ≤ i)
    (hi : i < 2 * (codes (p.select q)).width)
    (r : Registers (codes (p.select q)).width) (tape : BitTape) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨i, by omega⟩, r) tape) =
    some (readCfg p codes q base (⟨i + 1, by omega⟩, r) (tape.move .left)) := by
  have hn : ¬ i < (codes (p.select q)).width := by omega
  simp [controlStep, controller, readCfg, reading, hn, hi, applyAction,
    Function.update_idem]

theorem read_trace (q : Q) (base : Fin t → BitTape)
    (r : Registers (codes (p.select q)).width) (tape : BitTape) :
    Trace (controlStep (controller p codes decode)) (2 * (codes (p.select q)).width)
      (readCfg p codes q base (0, r) tape)
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩,
        fun i => tape.nth i.val) tape) :=
  reader_fragment_trace _ _ (readCfg p codes q base)
    (reader_scan_table p codes decode q base)
    (reader_back_table p codes decode q base) r tape

theorem action_table (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (base : Fin t → BitTape) (i : ℕ)
    (hi : i < (mutationActions (codes k) op).length) (tape : BitTape) :
    controlStep (controller p codes decode)
      (actionCfg p codes k q op base ⟨i, by omega⟩ tape) =
    some (actionCfg p codes k q op base ⟨i + 1, by omega⟩
      (applyAction (mutationActions (codes k) op)[i] tape)) := by
  simp [controlStep, controller, actionCfg, acting, hi, Function.update_idem]

theorem action_trace (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (base : Fin t → BitTape) (tape : BitTape) :
    Trace (controlStep (controller p codes decode)) (mutationActions (codes k) op).length
      (actionCfg p codes k q op base 0 tape)
      (actionCfg p codes k q op base
        ⟨(mutationActions (codes k) op).length, by omega⟩
        (execute (mutationActions (codes k) op) tape)) :=
  program_fragment_trace _ _ (actionCfg p codes k q op base)
    (action_table p codes decode k q op base) tape

end Fragments

section Assembly

variable {Q : Type} {t : ℕ} {Γ : Fin t → Type}
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

theorem dispatch_step (q : Q) (base : Fin t → BitTape) :
    controlStep (controller p codes decode) ⟨.inr (ready q), base⟩ =
      some (readCfg p codes q base (0, fun _ => none) (base (p.select q))) := by
  simp [controlStep, controller, ready, readCfg, reading, applyAction, Tape.write_self]

theorem reader_halt_step (q : Q) (base : Fin t → BitTape)
    (r : Registers (codes (p.select q)).width) (answer : Bool)
    (h : p.transition q (decode (p.select q) (registerBits r)) = .inl answer) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩, r)
        (base (p.select q))) =
      some ⟨.inl answer, base⟩ := by
  have hn : ¬ 2 * (codes (p.select q)).width < (codes (p.select q)).width := by omega
  simp [controlStep, controller, readCfg, reading, hn, h]

theorem reader_action_step (q q' : Q) (base : Fin t → BitTape)
    (r : Registers (codes (p.select q)).width)
    (op : Mutation (Γ (p.select q)))
    (h : p.transition q (decode (p.select q) (registerBits r)) = .inr (q', op)) :
    controlStep (controller p codes decode)
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩, r)
        (base (p.select q))) =
      some (actionCfg p codes (p.select q) q' op base 0 (base (p.select q))) := by
  have hn : ¬ 2 * (codes (p.select q)).width < (codes (p.select q)).width := by omega
  simp [controlStep, controller, readCfg, reading, actionCfg, acting, hn, h,
    applyAction, Tape.write_self]

theorem action_return_step (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (base : Fin t → BitTape) (tape : BitTape) :
    controlStep (controller p codes decode)
      (actionCfg p codes k q op base
        ⟨(mutationActions (codes k) op).length, by omega⟩ tape) =
      some ⟨.inr (ready q), Function.update base k tape⟩ := by
  simp [controlStep, controller, actionCfg, acting, ready, applyAction, Tape.write_self]

theorem tapeEncoding_update (q : Q) (S : ∀ k, List (Γ k))
    (k : Fin t) (s : List (Γ k)) :
    tapeEncoding codes (⟨.inr q, Function.update S k s⟩ : StackCfg Q Γ) =
      Function.update (fun j => dataTape (encodeDataStack (codes j) (S j))) k
        (dataTape (encodeDataStack (codes k) s)) := by
  funext j
  by_cases h : j = k
  · subst j
    simp [tapeEncoding]
  · simp [tapeEncoding, Function.update_of_ne h]

theorem action_execution (k : Fin t) (q : Q) (op : Mutation (Γ k))
    (S : ∀ k, List (Γ k)) :
    Trace (controlStep (controller p codes decode))
      ((mutationActions (codes k) op).length + 1)
      (actionCfg p codes k q op
        (fun j => dataTape (encodeDataStack (codes j) (S j))) 0
        (dataTape (encodeDataStack (codes k) (S k))))
      (encodeCfg p codes ⟨.inr q, Function.update S k (op.apply (S k))⟩) := by
  let base := fun j => dataTape (encodeDataStack (codes j) (S j))
  have hrun := action_trace p codes decode k q op base (base k)
  change Trace _ _ _ (actionCfg p codes k q op base _ _) at hrun
  have hcorrect :
      execute (mutationActions (codes k) op) (base k) =
        dataTape (encodeDataStack (codes k) (op.apply (S k))) :=
    mutationActions_correct (codes k) op (S k)
  rw [hcorrect] at hrun
  have hlast := action_return_step p codes decode k q op base
    (dataTape (encodeDataStack (codes k) (op.apply (S k))))
  have hall := hrun.trans (Trace.cons hlast (Trace.refl _))
  simpa only [encodeCfg, Sum.map_inr, tapeEncoding_update, base, ready] using hall

theorem read_entry_trace (q : Q) (base : Fin t → BitTape) :
    Trace (controlStep (controller p codes decode))
      (1 + 2 * (codes (p.select q)).width)
      ⟨.inr (ready q), base⟩
      (readCfg p codes q base (⟨2 * (codes (p.select q)).width, by omega⟩,
        fun i => (base (p.select q)).nth i.val) (base (p.select q))) :=
  (Trace.cons (dispatch_step p codes decode q base) (Trace.refl _)).trans
    (read_trace p codes decode q base (fun _ => none) (base (p.select q)))

end Assembly

/-- This bound is fixed by the finite stack alphabet codes. -/
def compilerOverhead {t : ℕ} {Γ : Fin t → Type} (codes : CodeFamily Γ) : ℕ :=
  (Finset.univ : Finset (Fin t)).sup (fun k => 4 * (codes k).width + 3)

theorem localCost_le_overhead {t : ℕ} {Γ : Fin t → Type}
    (codes : CodeFamily Γ) (k : Fin t) :
    4 * (codes k).width + 3 ≤ compilerOverhead codes :=
  Finset.le_sup (f := fun k => 4 * (codes k).width + 3) (Finset.mem_univ k)

theorem compilerOverhead_pos {Q : Type} {t : ℕ} {Γ : Fin t → Type}
    (p : StackProgram Q Γ) (codes : CodeFamily Γ) : 0 < compilerOverhead codes :=
  lt_of_lt_of_le (by omega) (localCost_le_overhead codes p.inputTape)

section Simulation

variable {Q : Type} {t : ℕ} {Γ : Fin t → Type}
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))
  (decode_nil : ∀ k, decode k [] = none)
  (decode_block : ∀ k a, decode k ((codes k).block a) = some a)

include decode_nil decode_block

/-- One source stack transition is implemented by actual primitive transitions. -/
theorem one_step_execution {a b : StackCfg Q Γ}
    (hstep : stackStep p a = some b) :
    RunsIn (controlStep (controller p codes decode)) (compilerOverhead codes)
      (encodeCfg p codes a) (encodeCfg p codes b) := by
  rcases a with ⟨state, S⟩
  cases state with
  | inl answer => simp [stackStep] at hstep
  | inr q =>
      let base : Fin t → BitTape := fun k => dataTape (encodeDataStack (codes k) (S k))
      let regs : Registers (codes (p.select q)).width :=
        fun i => (base (p.select q)).nth i.val
      have hdecode : decode (p.select q) (registerBits regs) = (S (p.select q)).head? :=
        decode_registers (codes (p.select q)) (decode (p.select q))
          (decode_nil (p.select q)) (decode_block (p.select q)) (S (p.select q))
      have hread := read_entry_trace p codes decode q base
      cases hd : p.transition q (S (p.select q)).head? with
      | inl answer =>
          simp only [stackStep, hd, Option.some.injEq] at hstep
          subst b
          have hlast := reader_halt_step p codes decode q base regs answer
            (by rw [hdecode]; exact hd)
          have hall := hread.trans (Trace.cons hlast (Trace.refl _))
          refine ⟨1 + 2 * (codes (p.select q)).width + 1, ?_, ?_⟩
          · exact le_trans (by omega) (localCost_le_overhead codes (p.select q))
          · change Trace (controlStep (controller p codes decode))
              (1 + 2 * (codes (p.select q)).width + 1)
              ⟨.inr (ready q), base⟩ ⟨.inl answer, base⟩
            simpa only [Nat.zero_add] using hall
      | inr next =>
          rcases next with ⟨q', op⟩
          simp only [stackStep, hd, Option.some.injEq] at hstep
          subst b
          have hdispatch := reader_action_step p codes decode q q' base regs op
            (by rw [hdecode]; exact hd)
          have hwork := action_execution p codes decode (p.select q) q' op S
          have hall := hread.trans ((Trace.cons hdispatch (Trace.refl _)).trans hwork)
          refine ⟨(1 + 2 * (codes (p.select q)).width) +
            (1 + ((mutationActions (codes (p.select q)) op).length + 1)), ?_, ?_⟩
          · have hlen := mutationActions_length (codes (p.select q)) op
            exact le_trans (by omega) (localCost_le_overhead codes (p.select q))
          · change Trace (controlStep (controller p codes decode))
              ((1 + 2 * (codes (p.select q)).width) +
                (1 + ((mutationActions (codes (p.select q)) op).length + 1)))
              ⟨.inr (ready q), base⟩
              (encodeCfg p codes
                ⟨.inr q', Function.update S (p.select q) (op.apply (S (p.select q)))⟩)
            simpa only [Nat.zero_add, encodeCfg, Sum.map_inr] using hall

/-- The simulation theorem does not assume a cost annotation for stack operations. -/
theorem controller_simulation :
    BoundedSimulation (stackStep p) (controlStep (controller p codes decode))
      (fun a b => b = encodeCfg p codes a) (compilerOverhead codes) := by
  intro a a' b hb hstep
  subst b
  exact ⟨encodeCfg p codes a', rfl,
    one_step_execution p codes decode decode_nil decode_block hstep⟩

end Simulation

section FiniteController

variable {Q : Type} [Fintype Q] {t : ℕ} {Γ : Fin t → Type}
  [∀ k, Fintype (Γ k)]
  (p : StackProgram Q Γ) (codes : CodeFamily Γ)
  (decode : ∀ k, List Bool → Option (Γ k))

instance stateFintype : Fintype (State p codes) := inferInstance

/-- The assembled finite control is a genuine primitive bit machine. -/
noncomputable def compiledMachine : PrimitiveMachine :=
  reindex (Fintype.equivFin (State p codes)) (controller p codes decode)

noncomputable def compiledCfg (a : StackCfg Q Γ) : (compiledMachine p codes decode).Cfg :=
  reindexCfg (Fintype.equivFin (State p codes)) (controller p codes decode)
    (encodeCfg p codes a)

/-- Reindexing the finite controller changes no primitive transition counts. -/
theorem primitive_one_step
    (decode_nil : ∀ k, decode k [] = none)
    (decode_block : ∀ k a, decode k ((codes k).block a) = some a)
    {a b : StackCfg Q Γ} (hstep : stackStep p a = some b) :
    RunsIn (compiledMachine p codes decode).step (compilerOverhead codes)
      (compiledCfg p codes decode a) (compiledCfg p codes decode b) := by
  obtain ⟨steps, hsteps, htrace⟩ :=
    one_step_execution p codes decode decode_nil decode_block hstep
  exact ⟨steps, hsteps, reindex_trace _ _ htrace⟩

theorem primitive_simulation
    (decode_nil : ∀ k, decode k [] = none)
    (decode_block : ∀ k a, decode k ((codes k).block a) = some a) :
    BoundedSimulation (stackStep p) (compiledMachine p codes decode).step
      (fun a b => b = compiledCfg p codes decode a) (compilerOverhead codes) := by
  intro a a' b hb hstep
  subst b
  exact ⟨compiledCfg p codes decode a', rfl,
    primitive_one_step p codes decode decode_nil decode_block hstep⟩

/-- Width-one input coding identifies the simulated input with the physical raw input. -/
theorem compiled_initial (inputAlphabet : Γ p.inputTape ≃ Bool)
    (code_input : codes p.inputTape = codeOfBoolEquiv inputAlphabet)
    (input : List Bool) :
    compiledCfg p codes decode (initialCfg p inputAlphabet input) =
      (compiledMachine p codes decode).init input := by
  have htapes :
      tapeEncoding codes (initialCfg p inputAlphabet input) =
        fun k => if k = p.inputTape then Tape.mk₁ (input.map some) else Tape.mk₁ [] := by
    funext k
    by_cases hk : k = p.inputTape
    · subst k
      simp only [tapeEncoding, initialCfg, Function.update_self, code_input, ↓reduceIte]
      exact dataTape_input inputAlphabet input
    · simp [tapeEncoding, initialCfg, hk, dataTape]
  unfold compiledCfg reindexCfg encodeCfg
  rw [htapes]
  rfl

theorem compiled_terminal (a : StackCfg Q Γ) (answer : Bool)
    (ha : a.state = .inl answer) :
    (compiledCfg p codes decode a).state = .inl answer := by
  unfold compiledCfg reindexCfg encodeCfg
  rw [ha]
  rfl

/--
An actual source execution on raw input becomes an actual primitive-bit
execution with machine-fixed multiplicative overhead and the same answer.
-/
theorem output_execution
    (decode_nil : ∀ k, decode k [] = none)
    (decode_block : ∀ k a, decode k ((codes k).block a) = some a)
    (inputAlphabet : Γ p.inputTape ≃ Bool)
    (code_input : codes p.inputTape = codeOfBoolEquiv inputAlphabet)
    (input : List Bool) (answer : Bool) (time : ℕ)
    (final : StackCfg Q Γ)
    (hrun : RunsIn (stackStep p) time (initialCfg p inputAlphabet input) final)
    (hanswer : final.state = .inl answer) :
    (compiledMachine p codes decode).OutputsInTime input answer
      (compilerOverhead codes * time) := by
  obtain ⟨c, hc, hsteps⟩ := simulate_runsIn
    (primitive_simulation p codes decode decode_nil decode_block) hrun rfl
  subst c
  refine ⟨compiledCfg p codes decode final, ?_, compiled_terminal p codes decode final answer hanswer⟩
  simpa only [compiled_initial p codes decode inputAlphabet code_input input] using hsteps

end FiniteController

end SubexponentialSAT.StackCompiler

end OAI.Algorithms
