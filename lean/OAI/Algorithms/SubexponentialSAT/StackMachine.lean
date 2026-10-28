import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.StackEncoding

namespace OAI.Algorithms

/-!
Actual primitive tape programs for encoded stacks. Every instruction below is
one move or one write of `Computation.PrimitiveMachine`; the measured traces
are derived from that transition function.
-/

namespace SubexponentialSAT.StackMachine

open Turing SubexponentialSAT.Computation

abbrev BitTape := Turing.Tape (Option Bool)
abbrev Action := Turing.TM0.Stmt (Option Bool)

def applyAction (action : Action) (tape : BitTape) : BitTape :=
  match action with
  | .move d => tape.move d
  | .write b => tape.write b

def execute : List Action → BitTape → BitTape
  | [], tape => tape
  | action :: rest, tape => execute rest (applyAction action tape)

@[simp] theorem execute_nil (tape : BitTape) : execute [] tape = tape := rfl

@[simp] theorem execute_cons (action : Action) (rest : List Action) (tape : BitTape) :
    execute (action :: rest) tape = execute rest (applyAction action tape) := rfl

theorem execute_append (first second : List Action) (tape : BitTape) :
    execute (first ++ second) tape = execute second (execute first tape) := by
  induction first generalizing tape with
  | nil => rfl
  | cons action rest ih => exact ih (applyAction action tape)

/-- A completely specified finite-control primitive program. Its last control
state is a return boundary; executing once more halts with `false`. -/
def program (actions : List Action) : PrimitiveMachine where
  tapeCount := 1
  stateCount := actions.length + 1
  inputTape := 0
  start := 0
  scan _ := 0
  transition q _ :=
    if h : q.val < actions.length then
      .inr (⟨q.val + 1, by omega⟩, actions[q.val])
    else .inl false

def programCfg (actions : List Action) (i : ℕ) (hi : i ≤ actions.length)
    (tape : BitTape) : (program actions).Cfg :=
  ⟨.inr ⟨i, by change i < actions.length + 1; omega⟩, fun _ => tape⟩

theorem program_step (actions : List Action) (i : ℕ) (hi : i < actions.length)
    (tape : BitTape) :
    (program actions).step (programCfg actions i hi.le tape) =
      some (programCfg actions (i + 1) (by omega) (applyAction actions[i] tape)) := by
  simp only [PrimitiveMachine.step, programCfg, program, hi, dite_eq_left]
  congr 1
  cases hact : actions[i] with
  | move d =>
    simp only [applyAction ]
    congr 1
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    change tape.move d = tape.move d
    rfl
  | write b =>
    simp only [applyAction ]
    congr 1
    funext k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    change tape.write b = tape.write b
    rfl

theorem program_trace_prefix (actions : List Action) (n : ℕ)
    (hn : n ≤ actions.length) (tape : BitTape) :
    Trace (program actions).step n
      (programCfg actions 0 (Nat.zero_le _) tape)
      (programCfg actions n hn (execute (actions.take n) tape)) := by
  induction n with
  | zero => exact Trace.refl _
  | succ n ih =>
    have hlt : n < actions.length := by omega
    have hrun := ih hlt.le
    have hstep : Trace (program actions).step 1
        (programCfg actions n hlt.le (execute (actions.take n) tape))
        (programCfg actions (n + 1) hn
          (applyAction actions[n] (execute (actions.take n) tape))) :=
      Trace.cons (program_step actions n hlt _) (Trace.refl _)
    have h := hrun.trans hstep
    simpa only [List.take_succ_eq_append_getElem hlt, execute_append,
      execute_cons, execute_nil] using h

/-- Exact, rather than annotated, cost of the straight-line primitive program. -/
theorem program_trace (actions : List Action) (tape : BitTape) :
    Trace (program actions).step actions.length
      (programCfg actions 0 (Nat.zero_le _) tape)
      (programCfg actions actions.length le_rfl (execute actions tape)) := by
  simpa using program_trace_prefix actions actions.length le_rfl tape

/-- All cells left of this representation are blank. There is no extra binary
sentinel, so a width-one Boolean code agrees with the actual raw input tape. -/
def dataTape (bits : List Bool) : BitTape := Tape.mk₁ (bits.map some)

theorem push_bit (bit : Bool) (bits : List Bool) :
    ((dataTape bits).move .left).write (some bit) = dataTape (bit :: bits) := by
  unfold dataTape Tape.mk₁ Tape.mk₂
  rw [Tape.move_left_mk']
  change (Tape.mk' (ListBlank.mk []) ((ListBlank.mk (bits.map some)).cons none)).write
    (some bit) = _
  rw [Tape.write_mk']
  rfl

theorem pop_bit (bit : Bool) (bits : List Bool) :
    ((dataTape (bit :: bits)).write none).move .right = dataTape bits := by
  unfold dataTape Tape.mk₁ Tape.mk₂
  change ((Tape.mk' (ListBlank.mk [])
    ((ListBlank.mk (bits.map some)).cons (some bit))).write none).move .right = _
  rw [Tape.write_mk', Tape.move_right_mk']
  simp only [ListBlank.head_cons, ListBlank.tail_cons]
  have hblank : (ListBlank.mk ([] : List (Option Bool))).cons none = ListBlank.mk [] := by
    have hdefault : (default : Option Bool) = none := rfl
    simpa [hdefault] using
      ListBlank.cons_head_tail (ListBlank.mk ([] : List (Option Bool)))
  rw [hblank]

def pushBits : List Bool → List Action
  | [] => []
  | bit :: bits => pushBits bits ++ [.move .left, .write (some bit)]

@[simp] theorem length_pushBits (bits : List Bool) :
    (pushBits bits).length = 2 * bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [pushBits, ih]; omega

theorem execute_pushBits (bits tail : List Bool) :
    execute (pushBits bits) (dataTape tail) = dataTape (bits ++ tail) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simp only [pushBits, execute_append, ih, execute_cons, execute_nil, applyAction]
    exact push_bit bit (bits ++ tail)

def popBits : ℕ → List Action
  | 0 => []
  | n + 1 => [.write none, .move .right] ++ popBits n

@[simp] theorem length_popBits (n : ℕ) : (popBits n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [popBits, ih]; omega

theorem execute_popBits (bits tail : List Bool) :
    execute (popBits bits.length) (dataTape (bits ++ tail)) = dataTape tail := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    simpa only [List.length_cons, popBits, List.cons_append, execute_append,
      execute_cons, execute_nil, applyAction, pop_bit] using ih

theorem pushBits_trace (bits tail : List Bool) :
    Trace (program (pushBits bits)).step (2 * bits.length)
      (programCfg (pushBits bits) 0 (Nat.zero_le _) (dataTape tail))
      (programCfg (pushBits bits) (pushBits bits).length le_rfl (dataTape (bits ++ tail))) := by
  simpa only [length_pushBits, execute_pushBits] using
    program_trace (pushBits bits) (dataTape tail)

theorem popBits_trace (bits tail : List Bool) :
    Trace (program (popBits bits.length)).step (2 * bits.length)
      (programCfg (popBits bits.length) 0 (Nat.zero_le _) (dataTape (bits ++ tail)))
      (programCfg (popBits bits.length) (popBits bits.length).length le_rfl (dataTape tail)) := by
  simpa only [length_popBits, execute_popBits] using
    program_trace (popBits bits.length) (dataTape (bits ++ tail))

/-! Reindexing a genuinely finite controller changes no primitive actions. -/

universe u

structure Controller (Q : Type u) (tapeCount : ℕ) where
  inputTape : Fin tapeCount
  start : Q
  scan : Q → Fin tapeCount
  transition : Q → Option Bool → Bool ⊕ (Q × Action)

structure ControlCfg (Q : Type u) (tapeCount : ℕ) where
  state : Bool ⊕ Q
  tapes : Fin tapeCount → BitTape

def controlStep {Q : Type u} {t : ℕ} (p : Controller Q t)
    (c : ControlCfg Q t) : Option (ControlCfg Q t) :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    let k := p.scan q
    match p.transition q (c.tapes k).head with
    | .inl answer => some ⟨.inl answer, c.tapes⟩
    | .inr (q', action) =>
      some ⟨.inr q', Function.update c.tapes k (applyAction action (c.tapes k))⟩

theorem controlStep_action {Q : Type u} {t : ℕ} (p : Controller Q t)
    (q q' : Q) (action : Action) (tapes : Fin t → BitTape)
    (h : p.transition q (tapes (p.scan q)).head = .inr (q', action)) :
    controlStep p ⟨.inr q, tapes⟩ = some ⟨.inr q',
      Function.update tapes (p.scan q) (applyAction action (tapes (p.scan q)))⟩ := by
  simp only [controlStep, h]

theorem controlStep_halt {Q : Type u} {t : ℕ} (p : Controller Q t)
    (q : Q) (answer : Bool) (tapes : Fin t → BitTape)
    (h : p.transition q (tapes (p.scan q)).head = .inl answer) :
    controlStep p ⟨.inr q, tapes⟩ = some ⟨.inl answer, tapes⟩ := by
  simp only [controlStep, h]

/-- A finite-control dispatch may preserve every tape by writing back the
single cell that its transition actually observes. This still costs one step. -/
theorem controlStep_write_self {Q : Type u} {t : ℕ} (p : Controller Q t)
    (q q' : Q) (tapes : Fin t → BitTape)
    (h : p.transition q (tapes (p.scan q)).head =
      .inr (q', .write (tapes (p.scan q)).head)) :
    controlStep p ⟨.inr q, tapes⟩ = some ⟨.inr q', tapes⟩ := by
  simpa only [applyAction, Tape.write_self, Function.update_eq_self] using
    controlStep_action p q q' (.write (tapes (p.scan q)).head) tapes h

def reindex {Q : Type u} {t n : ℕ} (e : Q ≃ Fin n) (p : Controller Q t) :
    PrimitiveMachine where
  tapeCount := t
  stateCount := n
  inputTape := p.inputTape
  start := e p.start
  scan q := p.scan (e.symm q)
  transition q b :=
    match p.transition (e.symm q) b with
    | .inl answer => .inl answer
    | .inr (q', action) => .inr (e q', action)

def reindexCfg {Q : Type u} {t n : ℕ} (e : Q ≃ Fin n) (p : Controller Q t)
    (c : ControlCfg Q t) : (reindex e p).Cfg :=
  ⟨match c.state with | .inl b => .inl b | .inr q => .inr (e q), c.tapes⟩

theorem reindex_step {Q : Type u} {t n : ℕ} (e : Q ≃ Fin n)
    (p : Controller Q t) (c : ControlCfg Q t) :
    (reindex e p).step (reindexCfg e p c) = (controlStep p c).map (reindexCfg e p) := by
  rcases c with ⟨state, tapes⟩
  cases state with
  | inl b => rfl
  | inr q =>
    simp only [PrimitiveMachine.step, reindexCfg, reindex, controlStep,
      Equiv.symm_apply_apply]
    cases h : p.transition q (tapes (p.scan q)).head with
    | inl b => rfl
    | inr qa =>
      rcases qa with ⟨q', action⟩
      cases action <;> rfl

theorem reindex_trace {Q : Type u} {t n steps : ℕ} (e : Q ≃ Fin n)
    (p : Controller Q t) {a b : ControlCfg Q t}
    (h : Trace (controlStep p) steps a b) :
    Trace (reindex e p).step steps (reindexCfg e p a) (reindexCfg e p b) := by
  induction h with
  | refl a => exact Trace.refl _
  | cons hs ht ih =>
    apply Trace.cons _ ih
    rw [reindex_step, hs]
    rfl

theorem update_single_tape (tape next : BitTape) :
    Function.update (fun _ : Fin 1 => tape) 0 next = (fun _ => next) := by
  funext k
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  simp

/-! A block reader uses one right move per bit, stores the observed bit in its
finite control, then performs the same number of left moves. -/

abbrev Registers (width : ℕ) := Fin width → Option Bool
abbrev ReaderState (width : ℕ) := Fin (2 * width + 1) × Registers width

def readerControl (width : ℕ) : Controller (ReaderState width) 1 where
  inputTape := 0
  start := (0, fun _ => none)
  scan _ := 0
  transition q bit :=
    if h : q.1.val < width then
      .inr ((⟨q.1.val + 1, by omega⟩, Function.update q.2 ⟨q.1.val, h⟩ bit),
        .move .right)
    else if h' : q.1.val < 2 * width then
      .inr ((⟨q.1.val + 1, by omega⟩, q.2), .move .left)
    else .inl false

def readerCfg (width i : ℕ) (hi : i ≤ 2 * width)
    (registers : Registers width) (tape : BitTape) : ControlCfg (ReaderState width) 1 :=
  ⟨.inr (⟨i, by omega⟩, registers), fun _ => tape⟩

theorem reader_scan_step (width i : ℕ) (hi : i < width)
    (registers : Registers width) (tape : BitTape) :
    controlStep (readerControl width) (readerCfg width i (by omega) registers tape) =
      some (readerCfg width (i + 1) (by omega)
        (Function.update registers ⟨i, hi⟩ tape.head) (tape.move .right)) := by
  simp [controlStep, readerControl, readerCfg, hi, applyAction, update_single_tape]

theorem reader_back_step (width i : ℕ) (hlo : width ≤ i) (hi : i < 2 * width)
    (registers : Registers width) (tape : BitTape) :
    controlStep (readerControl width) (readerCfg width i hi.le registers tape) =
      some (readerCfg width (i + 1) (by omega) registers (tape.move .left)) := by
  have hnot : ¬ i < width := by omega
  simp [controlStep, readerControl, readerCfg, hnot, hi, applyAction, update_single_tape]

def readPrefix {width : ℕ} (registers : Registers width) (tape : BitTape)
    (n : ℕ) : Registers width :=
  fun i => if i.val < n then tape.nth i.val else registers i

@[simp] theorem readPrefix_zero {width : ℕ} (registers : Registers width) (tape : BitTape) :
    readPrefix registers tape 0 = registers := by
  funext i
  simp [readPrefix]

@[simp] theorem readPrefix_full {width : ℕ} (registers : Registers width) (tape : BitTape) :
    readPrefix registers tape width = (fun i => tape.nth i.val) := by
  funext i
  simp [readPrefix, i.isLt]

theorem readPrefix_succ {width n : ℕ} (hn : n < width)
    (registers : Registers width) (tape : BitTape) :
    Function.update (readPrefix registers tape n) ⟨n, hn⟩ (tape.nth n) =
      readPrefix registers tape (n + 1) := by
  funext i
  by_cases heq : i = ⟨n, hn⟩
  · subst i
    simp [readPrefix]
  · have hne : i.val ≠ n := by
      intro h
      exact heq (Fin.ext h)
    rw [Function.update_of_ne heq]
    by_cases hlt : i.val < n
    · have hlt' : i.val < n + 1 := by omega
      simp [readPrefix, hlt, hlt']
    · have hlt' : ¬ i.val < n + 1 := by omega
      simp [readPrefix, hlt, hlt']

theorem reader_scan_trace (width n : ℕ) (hn : n ≤ width)
    (registers : Registers width) (tape : BitTape) :
    Trace (controlStep (readerControl width)) n
      (readerCfg width 0 (by omega) registers tape)
      (readerCfg width n (by omega) (readPrefix registers tape n)
        ((Tape.move .right)^[n] tape)) := by
  induction n with
  | zero =>
    simpa using (Trace.refl (step := controlStep (readerControl width))
      (readerCfg width 0 (by omega) registers tape))
  | succ n ih =>
    have hlt : n < width := by omega
    have hprev := ih hlt.le
    have hstep := reader_scan_step width n hlt
      (readPrefix registers tape n) ((Tape.move .right)^[n] tape)
    rw [Tape.move_right_n_head, readPrefix_succ hlt] at hstep
    have h := hprev.trans (Trace.cons hstep (Trace.refl _))
    simpa only [Function.iterate_succ_apply'] using h

theorem reader_back_trace (width n : ℕ) (hn : n ≤ width)
    (registers : Registers width) (tape : BitTape) :
    Trace (controlStep (readerControl width)) n
      (readerCfg width width (by omega) registers tape)
      (readerCfg width (width + n) (by omega) registers ((Tape.move .left)^[n] tape)) := by
  induction n with
  | zero => exact Trace.refl _
  | succ n ih =>
    have hlt : width + n < 2 * width := by omega
    have hprev := ih (by omega)
    have hstep := reader_back_step width (width + n) (by omega) hlt
      registers ((Tape.move .left)^[n] tape)
    have h := hprev.trans (Trace.cons hstep (Trace.refl _))
    simpa only [Nat.add_assoc, Function.iterate_succ_apply'] using h

theorem reader_control_trace (width : ℕ) (registers : Registers width) (tape : BitTape) :
    Trace (controlStep (readerControl width)) (2 * width)
      (readerCfg width 0 (by omega) registers tape)
      (readerCfg width (2 * width) le_rfl (fun i => tape.nth i.val) tape) := by
  have hscan := reader_scan_trace width width le_rfl registers tape
  rw [readPrefix_full] at hscan
  have hback := reader_back_trace width width le_rfl
    (fun i => tape.nth i.val) ((Tape.move .right)^[width] tape)
  have hinv : Function.LeftInverse (Tape.move .left : BitTape → BitTape)
      (Tape.move .right) := Tape.move_right_left
  have h := hscan.trans hback
  simpa only [hinv.iterate width tape, two_mul] using h

/-- This finite machine reads a fixed number of cells and restores the head. -/
noncomputable def reader (width : ℕ) : PrimitiveMachine :=
  reindex (Fintype.equivFin (ReaderState width)) (readerControl width)

theorem reader_trace (width : ℕ) (registers : Registers width) (tape : BitTape) :
    Trace (reader width).step (2 * width)
      (reindexCfg (Fintype.equivFin (ReaderState width)) (readerControl width)
        (readerCfg width 0 (by omega) registers tape))
      (reindexCfg (Fintype.equivFin (ReaderState width)) (readerControl width)
        (readerCfg width (2 * width) le_rfl (fun i => tape.nth i.val) tape)) :=
  reindex_trace _ _ (reader_control_trace width registers tape)

/-! Connecting the physical routines to the fixed alphabet encodings. -/

open SubexponentialSAT.StackEncoding

theorem pop_blank : ((dataTape []).write none).move .right = dataTape [] := by
  have hblank : (ListBlank.mk ([] : List (Option Bool))).cons none = ListBlank.mk [] := by
    have hdefault : (default : Option Bool) = none := rfl
    simpa [hdefault] using
      ListBlank.cons_head_tail (ListBlank.mk ([] : List (Option Bool)))
  change (Tape.mk' (ListBlank.mk []) (ListBlank.mk [])).move .right = _
  rw [Tape.move_right_mk']
  change Tape.mk' ((ListBlank.mk []).cons none) (ListBlank.mk []) = _
  rw [hblank]
  rfl

theorem execute_popBits_drop (n : ℕ) (bits : List Bool) :
    execute (popBits n) (dataTape bits) = dataTape (bits.drop n) := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    cases bits with
    | nil =>
      simpa only [popBits, execute_append, execute_cons, execute_nil, applyAction,
        pop_blank, List.drop_nil] using ih []
    | cons bit bits =>
      simpa only [popBits, execute_append, execute_cons, execute_nil, applyAction,
        pop_bit, List.drop_succ_cons] using ih bits

theorem pushSymbol_trace {α : Type u} (code : BlockCode α) (a : α) (s : List α) :
    Trace (program (pushBits (code.block a))).step (2 * code.width)
      (programCfg (pushBits (code.block a)) 0 (Nat.zero_le _)
        (dataTape (encodeDataStack code s)))
      (programCfg (pushBits (code.block a)) (pushBits (code.block a)).length le_rfl
        (dataTape (encodeDataStack code (a :: s)))) := by
  simpa only [code.length_block, encodeDataStack_cons] using
    pushBits_trace (code.block a) (encodeDataStack code s)

/-- Includes empty-stack pop: traversing blank cells leaves the canonical
empty tape unchanged. -/
theorem popSymbol_trace {α : Type u} (code : BlockCode α) (s : List α) :
    Trace (program (popBits code.width)).step (2 * code.width)
      (programCfg (popBits code.width) 0 (Nat.zero_le _) (dataTape (encodeDataStack code s)))
      (programCfg (popBits code.width) (popBits code.width).length le_rfl
        (dataTape (encodeDataStack code s.tail))) := by
  simpa only [length_popBits, execute_popBits_drop, drop_width_eq_tail] using
    program_trace (popBits code.width) (dataTape (encodeDataStack code s))

theorem dataTape_nth_append (bits tail : List Bool) (i : Fin bits.length) :
    (dataTape (bits ++ tail)).nth i.val = some bits[i.val] := by
  simp only [dataTape, Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]
  rw [List.getI_eq_getElem _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_append_left i.isLt]

@[simp] theorem dataTape_nil_nth (n : ℕ) : (dataTape []).nth n = none := by
  simp [dataTape, Tape.mk₁, Tape.mk₂, ListBlank.nth_mk]
  rfl

/-- A function on a fixed finite register space; not an unbounded list read. -/
def registerBits {width : ℕ} (registers : Registers width) : List Bool :=
  (List.ofFn registers).filterMap id

theorem registerBits_append (bits tail : List Bool) :
    registerBits (fun i : Fin bits.length => (dataTape (bits ++ tail)).nth i.val) = bits := by
  simp only [registerBits, dataTape_nth_append, List.ofFn_getElem_eq_map]
  simp

theorem registerBits_block {α : Type u} (code : BlockCode α) (a : α) (tail : List Bool) :
    registerBits (fun i : Fin code.width =>
      (dataTape (code.block a ++ tail)).nth i.val) = code.block a := by
  rw [← code.length_block a]
  exact registerBits_append (code.block a) tail

@[simp] theorem registerBits_blank (width : ℕ) :
    registerBits (fun i : Fin width => (dataTape []).nth i.val) = [] := by
  simp [registerBits, List.ofFn_const]

/-- The fixed block reader's final registers determine the exact source top
symbol, including `none` for an empty stack. -/
theorem decode_read_registers {α : Type u} {n : ℕ} (e : α ≃ Fin n) (s : List α) :
    readCodeOfEquiv e
      (registerBits (fun i : Fin (codeOfEquiv e).width =>
        (dataTape (encodeDataStack (codeOfEquiv e) s)).nth i.val)) = s.head? := by
  cases s with
  | nil =>
    change readCodeOfEquiv e (registerBits (fun i : Fin (codeOfEquiv e).width =>
      (dataTape []).nth i.val)) = none
    rw [registerBits_blank, readCodeOfEquiv_nil]
  | cons a s =>
    rw [encodeDataStack_cons, registerBits_block]
    exact readCodeOfEquiv_block e a

/-- Decoder-independent form, allowing the raw width-one input code and the
other work-stack codes to coexist in a single simulator. -/
theorem decode_registers {α : Type u} (code : BlockCode α)
    (decode : List Bool → Option α) (decode_nil : decode [] = none)
    (decode_block : ∀ a, decode (code.block a) = some a) (s : List α) :
    decode (registerBits (fun i : Fin code.width =>
      (dataTape (encodeDataStack code s)).nth i.val)) = s.head? := by
  cases s with
  | nil =>
    change decode (registerBits (fun i : Fin code.width => (dataTape []).nth i.val)) = none
    rw [registerBits_blank, decode_nil]
  | cons a s =>
    rw [encodeDataStack_cons, registerBits_block]
    exact decode_block a

theorem dataTape_input {α : Type u} (e : α ≃ Bool) (input : List Bool) :
    dataTape (encodeDataStack (codeOfBoolEquiv e) (input.map e.symm)) =
      Tape.mk₁ (input.map some) := by
  rw [encodeDataStack_codeOfBoolEquiv]
  simp [dataTape, List.map_map]

/-- One actual primitive reader run, together with the correctness of the
finite-control decoding of its output registers. -/
theorem readSymbol_trace {α : Type u} {n : ℕ} (e : α ≃ Fin n) (s : List α)
    (registers : Registers (codeOfEquiv e).width) :
    ∃ result : Registers (codeOfEquiv e).width,
      readCodeOfEquiv e (registerBits result) = s.head? ∧
      Trace (reader (codeOfEquiv e).width).step (2 * (codeOfEquiv e).width)
        (reindexCfg (Fintype.equivFin (ReaderState (codeOfEquiv e).width))
          (readerControl (codeOfEquiv e).width)
          (readerCfg (codeOfEquiv e).width 0 (by omega) registers
            (dataTape (encodeDataStack (codeOfEquiv e) s))))
        (reindexCfg (Fintype.equivFin (ReaderState (codeOfEquiv e).width))
          (readerControl (codeOfEquiv e).width)
          (readerCfg (codeOfEquiv e).width (2 * (codeOfEquiv e).width) le_rfl result
            (dataTape (encodeDataStack (codeOfEquiv e) s)))) := by
  refine ⟨fun i => (dataTape (encodeDataStack (codeOfEquiv e) s)).nth i.val,
    decode_read_registers e s, ?_⟩
  exact reader_trace (codeOfEquiv e).width registers _

/-! Inlining into a larger finite controller. The hypotheses below are
single-instruction transition-table equations, not assumed execution bounds.
They allow the final local control index to denote any caller continuation. -/

section ProgramFragment

variable {β : Type u} (step : β → Option β) (actions : List Action)
  (embed : Fin (actions.length + 1) → BitTape → β)
  (table : ∀ (i : ℕ) (hi : i < actions.length) (tape : BitTape),
    step (embed ⟨i, by omega⟩ tape) =
      some (embed ⟨i + 1, by omega⟩ (applyAction actions[i] tape)))

include table

theorem program_fragment_prefix (n : ℕ) (hn : n ≤ actions.length) (tape : BitTape) :
    Trace step n (embed 0 tape)
      (embed ⟨n, by omega⟩ (execute (actions.take n) tape)) := by
  induction n with
  | zero => exact Trace.refl _
  | succ n ih =>
    have hlt : n < actions.length := by omega
    have hprev := ih hlt.le
    have hstep := table n hlt (execute (actions.take n) tape)
    have h := hprev.trans (Trace.cons hstep (Trace.refl _))
    simpa only [List.take_succ_eq_append_getElem hlt, execute_append,
      execute_cons, execute_nil] using h

theorem program_fragment_trace (tape : BitTape) :
    Trace step actions.length (embed 0 tape)
      (embed ⟨actions.length, by omega⟩ (execute actions tape)) := by
  simpa only [List.take_length] using
    program_fragment_prefix step actions embed table actions.length le_rfl tape

end ProgramFragment

section ReaderFragment

variable {β : Type u} (step : β → Option β) (width : ℕ)
  (embed : ReaderState width → BitTape → β)
  (scanTable : ∀ (i : ℕ) (hi : i < width) (r : Registers width) (tape : BitTape),
    step (embed (⟨i, by omega⟩, r) tape) =
      some (embed (⟨i + 1, by omega⟩, Function.update r ⟨i, hi⟩ tape.head)
        (tape.move .right)))
  (backTable : ∀ (i : ℕ) (_hlo : width ≤ i) (hi : i < 2 * width)
    (r : Registers width) (tape : BitTape),
    step (embed (⟨i, by omega⟩, r) tape) =
      some (embed (⟨i + 1, by omega⟩, r) (tape.move .left)))

include scanTable in
theorem reader_fragment_scan (n : ℕ) (hn : n ≤ width)
    (registers : Registers width) (tape : BitTape) :
    Trace step n (embed (0, registers) tape)
      (embed (⟨n, by omega⟩, readPrefix registers tape n) ((Tape.move .right)^[n] tape)) := by
  induction n with
  | zero => simpa using (Trace.refl (step := step) (embed (0, registers) tape))
  | succ n ih =>
    have hlt : n < width := by omega
    have hprev := ih hlt.le
    have hstep := scanTable n hlt (readPrefix registers tape n) ((Tape.move .right)^[n] tape)
    rw [Tape.move_right_n_head, readPrefix_succ hlt] at hstep
    have h := hprev.trans (Trace.cons hstep (Trace.refl _))
    simpa only [Function.iterate_succ_apply'] using h

include backTable in
theorem reader_fragment_back (n : ℕ) (hn : n ≤ width)
    (registers : Registers width) (tape : BitTape) :
    Trace step n (embed (⟨width, by omega⟩, registers) tape)
      (embed (⟨width + n, by omega⟩, registers) ((Tape.move .left)^[n] tape)) := by
  induction n with
  | zero => exact Trace.refl _
  | succ n ih =>
    have hlt : width + n < 2 * width := by omega
    have hprev := ih (by omega)
    have hstep := backTable (width + n) (by omega) hlt registers ((Tape.move .left)^[n] tape)
    have h := hprev.trans (Trace.cons hstep (Trace.refl _))
    simpa only [Nat.add_assoc, Function.iterate_succ_apply'] using h

include scanTable backTable in
theorem reader_fragment_trace (registers : Registers width) (tape : BitTape) :
    Trace step (2 * width) (embed (0, registers) tape)
      (embed (⟨2 * width, by omega⟩, fun i => tape.nth i.val) tape) := by
  have hscan := reader_fragment_scan step width embed scanTable width le_rfl registers tape
  rw [readPrefix_full] at hscan
  have hback := reader_fragment_back step width embed backTable width le_rfl
    (fun i => tape.nth i.val) ((Tape.move .right)^[width] tape)
  have hinv : Function.LeftInverse (Tape.move .left : BitTape → BitTape)
      (Tape.move .right) := Tape.move_right_left
  have h := hscan.trans hback
  simpa only [hinv.iterate width tape, two_mul] using h

end ReaderFragment

end SubexponentialSAT.StackMachine

end OAI.Algorithms
