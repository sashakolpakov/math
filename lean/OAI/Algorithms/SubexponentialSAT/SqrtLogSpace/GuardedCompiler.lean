import OAI.Algorithms.SubexponentialSAT.BitProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.VisitedTape

/-! A width-one compilation of Boolean programs, with empty pop guarded before
the primitive stack compiler. The output contract reads the entire tape. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.StackCompiler OAI.Algorithms.SubexponentialSAT.StackEncoding OAI.Algorithms.SubexponentialSAT.StackMachine
open scoped BigOperators

abbrev State (r l : ℕ) := Fin l × (Fin r → Bool)

def selected {r s l : ℕ} (p : BitProgram.Program r s l) (q : State r l) : Fin s :=
  match p.code q.1 with
  | .halt => p.outputStack
  | .push stack _ _ | .peek stack _ _ _ | .pop stack _ _ _ => stack
  | _ => p.inputStack

def guardedPop : Option Bool → Mutation Bool
  | none => .keep
  | some _ => .pop

theorem guardedPop_apply (bits : List Bool) :
    (guardedPop bits.head?).apply bits = bits.tail := by
  cases bits <;> rfl

theorem guardedPop_empty_actions : mutationActions boolCode (guardedPop none) = [] := rfl

def transition {r s l : ℕ} (p : BitProgram.Program r s l) (q : State r l)
    (top : Option Bool) : Bool ⊕ (State r l × Mutation Bool) :=
  match p.code q.1 with
  | .halt => .inl (top.getD false)
  | .goto next => .inr ((next, q.2), .keep)
  | .set dst value next => .inr ((next, Function.update q.2 dst value), .keep)
  | .copy dst src next => .inr ((next, Function.update q.2 dst (q.2 src)), .keep)
  | .bnot dst src next => .inr ((next, Function.update q.2 dst (!(q.2 src))), .keep)
  | .band dst a b next => .inr ((next, Function.update q.2 dst (q.2 a && q.2 b)), .keep)
  | .bor dst a b next => .inr ((next, Function.update q.2 dst (q.2 a || q.2 b)), .keep)
  | .bxor dst a b next => .inr ((next, Function.update q.2 dst (q.2 a ^^ q.2 b)), .keep)
  | .branch test yes no => .inr (((if q.2 test then yes else no), q.2), .keep)
  | .push _ src next => .inr ((next, q.2), .push (q.2 src))
  | .peek _ value present next =>
      .inr ((next, BitProgram.readRegs q.2 value present top), .keep)
  | .pop _ value present next =>
      .inr ((next, BitProgram.readRegs q.2 value present top), guardedPop top)

def stackProgram {r s l : ℕ} (p : BitProgram.Program r s l) :
    StackProgram (State r l) (fun _ : Fin s => Bool) where
  inputTape := p.inputStack
  start := (p.entry, fun _ => false)
  select := selected p
  transition := transition p

theorem transition_empty_ne_pop {r s l : ℕ} (p : BitProgram.Program r s l)
    (q q' : State r l) : transition p q none ≠ .inr (q', .pop) := by
  cases h : p.code q.1 <;> simp [transition, h, guardedPop]

theorem push_actions (bit : Bool) :
    mutationActions boolCode (.push bit) = [.move .left, .write (some bit)] := rfl

theorem pop_actions : mutationActions boolCode .pop = [.write none, .move .right] := rfl

theorem mutation_displacement (displacement : Action → ℤ)
    (left : displacement (.move .left) = -1)
    (right : displacement (.move .right) = 1)
    (write : ∀ bit, displacement (.write bit) = 0)
    (op : Mutation Bool) (bits : List Bool) (safe : op = .pop → bits ≠ []) :
    ((mutationActions boolCode op).map displacement).sum =
      (bits.length : ℤ) - (op.apply bits).length := by
  cases op with
  | keep => simp [mutationActions, Mutation.apply]
  | pop =>
      cases bits with
      | nil => exact False.elim (safe rfl rfl)
      | cons bit bits => simp [pop_actions, Mutation.apply, right, write]
  | push bit => simp [push_actions, Mutation.apply, left, write]

theorem transition_mutation_displacement {r s l : ℕ} (p : BitProgram.Program r s l)
    (q q' : State r l) (op : Mutation Bool) (bits : List Bool)
    (h : transition p q bits.head? = .inr (q', op))
    (displacement : Action → ℤ)
    (left : displacement (.move .left) = -1)
    (right : displacement (.move .right) = 1)
    (write : ∀ bit, displacement (.write bit) = 0) :
    ((mutationActions boolCode op).map displacement).sum =
      (bits.length : ℤ) - (op.apply bits).length := by
  apply mutation_displacement displacement left right write
  intro hop hempty
  subst op
  subst bits
  exact transition_empty_ne_pop p q q' h

def stackCfg {r s l : ℕ} (p : BitProgram.Program r s l) (c : BitProgram.Cfg r s l) :
    StackCfg (State r l) (fun _ : Fin s => Bool) :=
  ⟨match c.pc with
    | none => .inl ((c.stacks p.outputStack).head?.getD false)
    | some label => .inr (label, c.regs), c.stacks⟩

theorem stack_step {r s l : ℕ} (p : BitProgram.Program r s l) (c : BitProgram.Cfg r s l) :
    stackStep (stackProgram p) (stackCfg p c) = (BitProgram.step p c).map (stackCfg p) := by
  rcases c with ⟨pc, regs, stk⟩
  cases pc with
  | none => rfl
  | some label =>
      cases h : p.code label <;>
        simp [stackStep, stackProgram, stackCfg, selected, transition, h,
          BitProgram.step, BitProgram.execInstr, Mutation.apply,
          Function.update_eq_self]
      exact congrArg (Function.update stk _) (guardedPop_apply _)

theorem stack_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : BitProgram.Cfg r s l} {n : ℕ} (h : BitProgram.Trace p n a b) :
    Trace (stackStep (stackProgram p)) n (stackCfg p a) (stackCfg p b) := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih =>
      apply Trace.cons _ ih
      rw [stack_step, hs]
      rfl

def codes (s : ℕ) : CodeFamily (fun _ : Fin s => Bool) := fun _ => boolCode

def decoder (s : ℕ) : (i : Fin s) → List Bool → Option Bool := fun _ => List.head?

theorem decoder_nil (s : ℕ) (i : Fin s) : decoder s i [] = none := rfl

theorem decoder_block (s : ℕ) (i : Fin s) (b : Bool) :
    decoder s i ((codes s i).block b) = some b := rfl

noncomputable abbrev primitive {r s l : ℕ} (p : BitProgram.Program r s l) : PrimitiveMachine :=
  reindex (Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s)))
    (controller (stackProgram p) (codes s) (decoder s))

noncomputable abbrev primitiveCfg {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) : (primitive p).Cfg :=
  reindexCfg (Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s)))
    (controller (stackProgram p) (codes s) (decoder s))
    (encodeCfg (stackProgram p) (codes s) (stackCfg p c))

noncomputable abbrev primitiveControlCfg {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : ControlCfg (StackCompiler.State (stackProgram p) (codes s)) s) :
    (primitive p).Cfg :=
  reindexCfg (Fintype.equivFin _) (controller (stackProgram p) (codes s) (decoder s)) c

@[simp] theorem reindex_tapeCount {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t) : (reindex e p).tapeCount = t := rfl

@[simp] theorem primitive_tapeCount {r s l : ℕ} (p : BitProgram.Program r s l) :
    (primitive p).tapeCount = s := rfl

theorem compiler_overhead {r s l : ℕ} (p : BitProgram.Program r s l) :
    compilerOverhead (codes s) = 7 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    rfl
  · exact localCost_le_overhead (codes s) p.inputStack

theorem primitive_execution {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : BitProgram.Cfg r s l} {n : ℕ} (h : BitProgram.RunsIn p n a b) :
    RunsIn (primitive p).step (7 * n) (primitiveCfg p a) (primitiveCfg p b) := by
  obtain ⟨steps, hsteps, htrace⟩ := h
  have hstack : RunsIn (stackStep (stackProgram p)) n (stackCfg p a) (stackCfg p b) :=
    ⟨steps, hsteps, stack_trace p htrace⟩
  obtain ⟨c, hc, hrun⟩ := simulate_runsIn
    (primitive_simulation (stackProgram p) (codes s) (decoder s)
      (decoder_nil s) (decoder_block s)) hstack rfl
  rw [hc] at hrun
  change RunsIn (primitive p).step (compilerOverhead (codes s) * n)
    (primitiveCfg p a) (primitiveCfg p b) at hrun
  simpa only [compiler_overhead p] using hrun

theorem primitive_initial {r s l : ℕ} (p : BitProgram.Program r s l) (input : List Bool) :
    primitiveCfg p (BitProgram.initial p input) = (primitive p).init input := by
  have h : stackCfg p (BitProgram.initial p input) =
      initialCfg (stackProgram p) (Equiv.refl Bool) input := by
    simp [stackCfg, initialCfg, stackProgram,
      Function.update_apply, funext_iff]
  unfold primitiveCfg primitive
  rw [h]
  exact compiled_initial (stackProgram p) (codes s) (decoder s) (Equiv.refl Bool) rfl input

theorem tapeEncoding_bool {r s l : ℕ}
    (a : StackCfg (State r l) (fun _ : Fin s => Bool)) :
    StackCompiler.tapeEncoding (codes s) a = fun i => dataTape (a.stk i) := by
  funext i
  exact congrArg dataTape (encodeDataStack_boolCode (a.stk i))

theorem primitive_tape {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) (i : Fin s) :
    (primitiveCfg p c).tapes i = Turing.Tape.mk₁ ((c.stacks i).map some) := by
  change dataTape (encodeDataStack boolCode (c.stacks i)) = _
  rw [encodeDataStack_boolCode]
  rfl

theorem primitive_halted {r s l : ℕ} (p : BitProgram.Program r s l)
    (c : BitProgram.Cfg r s l) (h : c.pc = none) :
    (primitiveCfg p c).state = .inl ((c.stacks p.outputStack).head?.getD false) := by
  apply compiled_terminal
  simp [stackCfg, h]

theorem primitive_word_execution {r s l : ℕ} (p : BitProgram.Program r s l)
    {input output : List Bool} {n : ℕ} {final : BitProgram.Cfg r s l}
    (h : BitProgram.RunsIn p n (BitProgram.initial p input) final)
    (halted : final.pc = none) (hout : final.stacks p.outputStack = output) :
    ∃ c : (primitive p).Cfg,
      RunsIn (primitive p).step (7 * n) ((primitive p).init input) c ∧
      c.state = .inl (output.head?.getD false) ∧
      c.tapes p.outputStack = Turing.Tape.mk₁ (output.map some) := by
  refine ⟨primitiveCfg p final, ?_, ?_, ?_⟩
  · simpa only [primitive_initial] using primitive_execution p h
  · rw [primitive_halted p final halted, hout]
  · rw [primitive_tape, hout]

theorem reindex_located_action {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t)
    (c : LocatedCfg (reindex e p)) (q q' : Q) (action : Action)
    (tapes : Fin t → BitTape)
    (hc : c.config = reindexCfg e p ⟨.inr q, tapes⟩)
    (ha : p.transition q (tapes (p.scan q)).head = .inr (q', action)) :
    ∃ d : LocatedCfg (reindex e p),
      locatedStep (reindex e p) c = some d ∧
      d.config = reindexCfg e p
        ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩ ∧
      d.position = Function.update c.position (p.scan q)
        (c.position (p.scan q) + headDisplacement action) := by
  have hs : (reindex e p).step c.config = some (reindexCfg e p
      ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩) := by
    rw [hc, reindex_step, controlStep_action p q q' action tapes ha]
    rfl
  let d := c.monitor (reindexCfg e p
    ⟨.inr q', Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩)
  have hstep : locatedStep (reindex e p) c = some d := by
    rw [locatedStep, hs]
    rfl
  refine ⟨d, hstep, c.monitor_config _, ?_⟩
  have htransition : (reindex e p).transition (e q)
      (c.config.tapes ((reindex e p).scan (e q))).head = .inr (e q', action) := by
    simp only [hc, reindexCfg, reindex, Equiv.symm_apply_apply, ha]
  have hposition := locatedStep_position_action hstep
    (show c.config.state = .inr (e q) by rw [hc]; rfl) htransition
  simpa only [reindex, Equiv.symm_apply_apply] using hposition

theorem reindex_located_halt {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t)
    (c : LocatedCfg (reindex e p)) (q : Q) (answer : Bool)
    (tapes : Fin t → BitTape)
    (hc : c.config = reindexCfg e p ⟨.inr q, tapes⟩)
    (ha : p.transition q (tapes (p.scan q)).head = .inl answer) :
    ∃ d : LocatedCfg (reindex e p),
      locatedStep (reindex e p) c = some d ∧
      d.config = reindexCfg e p ⟨.inl answer, tapes⟩ ∧ d.position = c.position := by
  have hs : (reindex e p).step c.config =
      some (reindexCfg e p ⟨.inl answer, tapes⟩) := by
    rw [hc, reindex_step, controlStep_halt p q answer tapes ha]
    rfl
  let d := c.monitor (reindexCfg e p ⟨.inl answer, tapes⟩)
  have hstep : locatedStep (reindex e p) c = some d := by
    rw [locatedStep, hs]
    rfl
  refine ⟨d, hstep, c.monitor_config _, ?_⟩
  apply locatedStep_position_halt (answer := answer) hstep
    (show c.config.state = .inr (e q) by rw [hc]; rfl)
  simp only [hc, reindexCfg, reindex, Equiv.symm_apply_apply, ha]

theorem reindex_located_fragment {Q : Type} {t states : ℕ}
    (e : Q ≃ Fin states) (p : Controller Q t) (count : ℕ)
    (state : ℕ → Q) (tapes : ℕ → Fin t → BitTape) (actions : ℕ → Action) (k : Fin t)
    (scan : ∀ i < count, p.scan (state i) = k)
    (next : ∀ i < count,
      p.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)))
    (c : LocatedCfg (reindex e p))
    (hc : c.config = reindexCfg e p ⟨.inr (state 0), tapes 0⟩) :
    ∃ d : LocatedCfg (reindex e p),
      Trace (locatedStep (reindex e p)) count c d ∧
      d.config = reindexCfg e p ⟨.inr (state count), tapes count⟩ ∧
      d.position = Function.update c.position k
        (c.position k + ∑ i ∈ Finset.range count, headDisplacement (actions i)) := by
  have prefixTrace (n : ℕ) (hn : n ≤ count) :
      ∃ d : LocatedCfg (reindex e p),
        Trace (locatedStep (reindex e p)) n c d ∧
        d.config = reindexCfg e p ⟨.inr (state n), tapes n⟩ ∧
        d.position = Function.update c.position k
          (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)) := by
    induction n with
    | zero =>
        refine ⟨c, .refl c, hc, ?_⟩
        simp only [Finset.sum_range_zero, add_zero]
        change (fun i : Fin t => c.position i) =
          Function.update (fun i : Fin t => c.position i) k (c.position k)
        exact (Function.update_eq_self k (fun i : Fin t => c.position i)).symm
    | succ n ih =>
        have hlt : n < count := by omega
        obtain ⟨middle, htrace, hconfig, hposition⟩ := ih (by omega)
        obtain ⟨ha, htapes⟩ := next n hlt
        obtain ⟨d, hstep, hdconfig, hdposition⟩ := reindex_located_action e p middle
          (state n) (state (n + 1)) (actions n) (tapes n) hconfig
          (by simpa only [scan n hlt] using ha)
        refine ⟨d, htrace.trans (.cons hstep (.refl d)), ?_, ?_⟩
        · simpa only [scan n hlt, ← htapes] using hdconfig
        · rw [scan n hlt, hposition] at hdposition
          rw [hdposition]
          change Function.update
              (Function.update (fun i : Fin t => c.position i) k
                (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)))
              k
              (Function.update (fun i : Fin t => c.position i) k
                  (c.position k + ∑ i ∈ Finset.range n, headDisplacement (actions i)) k +
                headDisplacement (actions n)) =
            Function.update (fun i : Fin t => c.position i) k
              (c.position k + ∑ i ∈ Finset.range (n + 1), headDisplacement (actions i))
          funext i
          by_cases hi : i = k
          · subst i
            simp only [Function.update_self, Finset.sum_range_succ]
            rw [add_assoc]
          · simp only [Function.update_of_ne hi]
  exact prefixTrace count le_rfl

theorem mutation_located_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    (k : Fin s) (q : State r l) (op : Mutation Bool)
    (base : Fin s → BitTape) (tape : BitTape)
    (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (actionCfg (stackProgram p) (codes s) k q op base 0 tape)) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) (mutationActions boolCode op).length c d ∧
      d.config = primitiveControlCfg p
        (actionCfg (stackProgram p) (codes s) k q op base
          ⟨(mutationActions boolCode op).length, Nat.lt_succ_self _⟩
          (execute (mutationActions boolCode op) tape)) ∧
      d.position = Function.update c.position k
        (c.position k + ((mutationActions boolCode op).map headDisplacement).sum) := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let state (i : ℕ) : StackCompiler.State (stackProgram p) (codes s) :=
    acting k q op ⟨min i 2, by
      change min i 2 < 3
      omega⟩
  let tapes (i : ℕ) := Function.update base k
    (execute ((mutationActions boolCode op).take i) tape)
  let actions (i : ℕ) := ((mutationActions boolCode op)[i]?).getD (.write none)
  have hscan : ∀ i < (mutationActions boolCode op).length, C.scan (state i) = k := by
    intro i _
    rfl
  have hnext : ∀ i < (mutationActions boolCode op).length,
      C.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)) := by
    intro i hi
    have hi2 : i < 2 := lt_of_lt_of_le hi (mutationActions_length boolCode op)
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      cases op <;>
      simp_all [C, state, tapes, actions, controller, acting, codes, boolCode,
        codeOfBoolEquiv, mutationActions, pushBits, popBits, execute, applyAction,
        Function.update_idem]
  obtain ⟨d, htrace, hconfig, hposition⟩ := reindex_located_fragment e C
    (mutationActions boolCode op).length state tapes actions k hscan hnext c
    (by simpa [primitive, primitiveControlCfg, actionCfg, state, tapes, e, C] using hc)
  refine ⟨d, htrace, ?_, ?_⟩
  · cases op <;>
      simpa [primitive, primitiveControlCfg, actionCfg, state, tapes, e, C, codes,
        mutationActions, boolCode, codeOfBoolEquiv, pushBits, popBits] using hconfig
  · cases op <;>
      simpa [primitive, actions, mutationActions, boolCode, codeOfBoolEquiv, pushBits, popBits,
        Finset.sum_range_succ, headDisplacement] using hposition

theorem reader_located_trace {r s l : ℕ} (p : BitProgram.Program r s l)
    (q : State r l) (base : Fin s → BitTape) (tape : BitTape)
    (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (readCfg (stackProgram p) (codes s) q base (0, fun _ => none) tape)) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) 2 c d ∧
      d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => tape.head) tape) ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let k := selected p q
  let state (i : ℕ) : StackCompiler.State (stackProgram p) (codes s) :=
    reading q (⟨min i 2, by change min i 2 < 3; omega⟩,
      if i = 0 then fun _ => none else fun _ => tape.head)
  let tapes (i : ℕ) := Function.update base k (if i = 1 then tape.move .right else tape)
  let actions (i : ℕ) : Action := if i = 0 then .move .right else .move .left
  have hscan : ∀ i < 2, C.scan (state i) = k := by
    intro i _
    rfl
  have hnext : ∀ i < 2,
      C.transition (state i) (tapes i k).head = .inr (state (i + 1), actions i) ∧
      tapes (i + 1) = Function.update (tapes i) k (applyAction (actions i) (tapes i k)) := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · simp [C, state, tapes, actions, k, controller, reading, stackProgram,
        codes, boolCode, codeOfBoolEquiv, applyAction,
        Function.update_idem]
      congr 4
      congr 2
      funext x
      fin_cases x
      change Function.update (fun _ : Fin 1 => none) 0 tape.head 0 = tape.head
      exact Function.update_self 0 tape.head (fun _ : Fin 1 => none)
    · simp [C, state, tapes, actions, k, controller, reading, stackProgram,
        codes, boolCode, codeOfBoolEquiv, applyAction,
        Function.update_idem]
  obtain ⟨d, htrace, hconfig, hposition⟩ := reindex_located_fragment e C
    2 state tapes actions k hscan hnext c
    (by
      change c.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base (0, fun _ => none) tape)
      exact hc)
  refine ⟨d, htrace, ?_, ?_⟩
  · change d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => tape.head) tape)
    exact hconfig
  · rw [hposition]
    have hsum : ∑ i ∈ Finset.range 2, headDisplacement (actions i) = 0 := by
      norm_num [Finset.sum_range_succ, actions, headDisplacement]
    rw [hsum, add_zero]
    change Function.update (fun i : Fin s => c.position i) k (c.position k) =
      (fun i : Fin s => c.position i)
    exact Function.update_eq_self k (fun i : Fin s => c.position i)

theorem read_entry_located {r s l : ℕ} (p : BitProgram.Program r s l)
    (q : State r l) (base : Fin s → BitTape) (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p ⟨.inr (ready q), base⟩) :
    ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) 3 c d ∧
      d.config = primitiveControlCfg p
        (readCfg (stackProgram p) (codes s) q base
          (⟨2, by change 2 < 3; decide⟩, fun _ => (base (selected p q)).head)
          (base (selected p q))) ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  obtain ⟨middle, hstep, hconfig, hposition⟩ := reindex_located_action e C c
    (ready q) (reading q (0, fun _ => none))
    (.write (base (selected p q)).head) base hc rfl
  have hscan : C.scan (ready q) = selected p q := rfl
  have hmiddle : middle.config = primitiveControlCfg p
      (readCfg (stackProgram p) (codes s) q base (0, fun _ => none)
        (base (selected p q))) := by
    rw [hscan] at hconfig
    simp only [applyAction, Turing.Tape.write_self, Function.update_eq_self] at hconfig
    simpa [primitive, primitiveControlCfg, readCfg, stackProgram, C, e,
      Function.update_eq_self] using hconfig
  obtain ⟨d, htrace, hdconfig, hdposition⟩ := reader_located_trace p q base
    (base (selected p q)) middle hmiddle
  refine ⟨d, .cons hstep htrace, hdconfig, ?_⟩
  rw [hdposition, hposition]
  simp only [headDisplacement, add_zero]
  change Function.update (fun i : Fin s => c.position i) (C.scan (ready q))
      (c.position (C.scan (ready q))) = (fun i : Fin s => c.position i)
  exact Function.update_eq_self (C.scan (ready q)) (fun i : Fin s => c.position i)

theorem decoder_head (s : ℕ) (k : Fin s) (top : Option Bool) :
    decoder s k (registerBits (fun _ : Fin 1 => top)) = top := by
  cases top <;> rfl

theorem dataTape_head (bits : List Bool) : (dataTape bits).head = bits.head? := by
  cases bits <;> rfl

theorem action_return_located {r s l : ℕ} (p : BitProgram.Program r s l)
    (k : Fin s) (q : State r l) (op : Mutation Bool)
    (base : Fin s → BitTape) (tape : BitTape) (c : LocatedCfg (primitive p))
    (hc : c.config = primitiveControlCfg p
      (actionCfg (stackProgram p) (codes s) k q op base
        ⟨(mutationActions boolCode op).length, Nat.lt_succ_self _⟩ tape)) :
    ∃ d : LocatedCfg (primitive p),
      locatedStep (primitive p) c = some d ∧
      d.config = primitiveControlCfg p ⟨.inr (ready q), Function.update base k tape⟩ ∧
      d.position = c.position := by
  let C := controller (stackProgram p) (codes s) (decoder s)
  let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
  let phase : Fin 3 := ⟨(mutationActions boolCode op).length,
    Nat.lt_succ_of_le (mutationActions_length boolCode op)⟩
  obtain ⟨d, hstep, hconfig, hposition⟩ := reindex_located_action e C c
    (acting k q op phase) (ready q) (.write tape.head) (Function.update base k tape) hc
    (by simp [C, controller, acting, phase, codes])
  refine ⟨d, hstep, ?_, ?_⟩
  · simpa [primitive, primitiveControlCfg, C, e, controller, acting, applyAction,
      Function.update_idem] using hconfig
  · rw [hposition]
    simp only [headDisplacement, add_zero]
    change Function.update (fun i : Fin s => c.position i) (C.scan (acting k q op phase))
        (c.position (C.scan (acting k q op phase))) = (fun i : Fin s => c.position i)
    exact Function.update_eq_self (C.scan (acting k q op phase))
      (fun i : Fin s => c.position i)

theorem stack_located_step {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : StackCfg (State r l) (fun _ : Fin s => Bool)}
    (hs : stackStep (stackProgram p) a = some b)
    {c : LocatedCfg (primitive p)}
    (hc : c.config = compiledCfg (stackProgram p) (codes s) (decoder s) a) :
    ∃ time ≤ 7, ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) time c d ∧
      d.config = compiledCfg (stackProgram p) (codes s) (decoder s) b ∧
      ∀ i : Fin s, d.position i = c.position i + (a.stk i).length - (b.stk i).length := by
  rcases a with ⟨state, S⟩
  cases state with
  | inl answer => simp [stackStep] at hs
  | inr q =>
    let C := controller (stackProgram p) (codes s) (decoder s)
    let e := Fintype.equivFin (StackCompiler.State (stackProgram p) (codes s))
    let k := selected p q
    let base := fun i => dataTape (S i)
    let readState : StackCompiler.State (stackProgram p) (codes s) :=
      reading q (⟨2, by change 2 < 3; decide⟩, fun _ => (base k).head)
    have hstart : c.config = primitiveControlCfg p ⟨.inr (ready q), base⟩ := by
      simpa only [compiledCfg, encodeCfg, primitiveControlCfg, tapeEncoding_bool,
        Sum.map_inr, base] using hc
    obtain ⟨readEnd, hread, hreadCfg, hreadPos⟩ := read_entry_located p q base c hstart
    have hr : readEnd.config = reindexCfg e C ⟨.inr readState, base⟩ := by
      simpa [primitiveControlCfg, readCfg, readState, stackProgram, k, C, e] using hreadCfg
    cases ht : transition p q (S k).head? with
    | inl answer =>
      dsimp only [k] at ht
      simp only [stackStep, stackProgram, ht, Option.some.injEq] at hs
      subst b
      obtain ⟨d, hlast, hconfig, hposition⟩ := reindex_located_halt e C readEnd
        readState answer base hr (by
          simp [C, controller, readState, reading, codes, boolCode, codeOfBoolEquiv,
            stackProgram, decoder_head, base, dataTape_head, k, ht])
      refine ⟨4, by omega, d, hread.trans (.cons hlast (.refl d)), ?_, ?_⟩
      · simpa only [primitive, compiledCfg, encodeCfg, primitiveControlCfg, tapeEncoding_bool,
          Sum.map_inl, id_eq, base, e, C] using hconfig
      · intro i
        rw [hposition, hreadPos]
        change c.position i = c.position i + (S i).length - (S i).length
        omega
    | inr output =>
      rcases output with ⟨q', op⟩
      dsimp only [k] at ht
      simp only [stackStep, stackProgram, ht, Option.some.injEq] at hs
      subst b
      obtain ⟨actionStart, hdispatch, hdispatchCfg, hdispatchPos⟩ :=
        reindex_located_action e C readEnd readState (acting k q' op 0)
          (.write (base k).head) base hr (by
            simp [C, controller, readState, reading, codes, boolCode, codeOfBoolEquiv,
              stackProgram, decoder_head, base, dataTape_head, k, ht]
            rfl)
      have hactionStart : actionStart.config = primitiveControlCfg p
          (actionCfg (stackProgram p) (codes s) k q' op base 0 (base k)) := by
        simpa [primitiveControlCfg, actionCfg, readState, C, e, controller, reading,
          stackProgram, k, applyAction, Function.update_eq_self] using hdispatchCfg
      have hdispatchPosition : actionStart.position = readEnd.position := by
        rw [hdispatchPos]
        simp only [headDisplacement, add_zero]
        change Function.update (fun i : Fin s => readEnd.position i) (C.scan readState)
            (readEnd.position (C.scan readState)) = (fun i : Fin s => readEnd.position i)
        exact Function.update_eq_self (C.scan readState) (fun i : Fin s => readEnd.position i)
      obtain ⟨actionEnd, haction, hactionCfg, hactionPos⟩ :=
        mutation_located_trace p k q' op base (base k) actionStart hactionStart
      obtain ⟨d, hreturn, hreturnCfg, hreturnPos⟩ := action_return_located p k q' op
        base (execute (mutationActions boolCode op) (base k)) actionEnd hactionCfg
      have htape : execute (mutationActions boolCode op) (base k) =
          dataTape (op.apply (S k)) := by
        simpa only [base, encodeDataStack_boolCode] using mutationActions_correct boolCode op (S k)
      refine ⟨3 + (1 + ((mutationActions boolCode op).length + 1)), ?_, d,
        hread.trans ((Trace.cons hdispatch (Trace.refl actionStart)).trans
          (haction.trans (.cons hreturn (.refl d)))), ?_, ?_⟩
      · have hlength := mutationActions_length boolCode op
        change (mutationActions boolCode op).length ≤ 2 at hlength
        omega
      · rw [htape] at hreturnCfg
        change d.config = primitiveControlCfg p
          ⟨.inr (ready q'), fun i => dataTape (encodeDataStack boolCode
            ((Function.update S k (op.apply (S k))) i))⟩
        simp_rw [encodeDataStack_boolCode]
        have htapes : (fun i => dataTape ((Function.update S k (op.apply (S k))) i)) =
            Function.update base k (dataTape (op.apply (S k))) :=
          Function.comp_update dataTape S k (op.apply (S k))
        rw [htapes]
        exact hreturnCfg
      · intro i
        rw [hreturnPos, hactionPos, hdispatchPosition, hreadPos]
        rw [transition_mutation_displacement p q q' op (S k) ht
          headDisplacement rfl rfl (fun _ => rfl)]
        change Function.update c.position k
          (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) i =
            c.position i + (S i).length - ((Function.update S k (op.apply (S k))) i).length
        by_cases hi : i = k
        · subst i
          change Function.update (fun j : Fin s => c.position j) k
              (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) k =
            c.position k + (S k).length -
              (Function.update S k (op.apply (S k)) k).length
          simp only [Function.update_self]
          omega
        · change Function.update (fun j : Fin s => c.position j) k
              (c.position k + (((S k).length : ℤ) - (op.apply (S k)).length)) i =
            c.position i + (S i).length -
              (Function.update S k (op.apply (S k)) i).length
          simp only [Function.update_of_ne hi]
          omega

theorem primitive_located_step {r s l : ℕ} (p : BitProgram.Program r s l)
    {a b : BitProgram.Cfg r s l} (hs : BitProgram.step p a = some b)
    {c : LocatedCfg (primitive p)} (hc : c.config = primitiveCfg p a) :
    ∃ time ≤ 7, ∃ d : LocatedCfg (primitive p),
      Trace (locatedStep (primitive p)) time c d ∧ d.config = primitiveCfg p b ∧
      ∀ i : Fin s, d.position i = c.position i + (a.stacks i).length - (b.stacks i).length := by
  apply stack_located_step p (a := stackCfg p a) (b := stackCfg p b) _ hc
  rw [stack_step, hs]
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler
