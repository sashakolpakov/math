import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTCofactorControl

namespace OAI.Algorithms

/-! Exact stack transport and finite-loop composition for CRT scalar cofactors.
The arithmetic premises are executions of supplied finite command tables;
the concrete machine instantiates them with the actual scalar services. -/

namespace SubexponentialSAT.SubexpCRTCofactorLoop

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives
open SubexpCRTCofactorControl

theorem clear_eval (d : Data) (src : Fin 110) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩ := by
  apply Eval.call
  have ht := clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := halt_after_trace _ ht 2 rfl rfl
  simpa [clearResult, clearStacks, StructuredProgram.State.withPC,
    clearProgram, Nat.add_assoc] using hh

abbrev prepareOperands : Cmd 8 110 := .seq (move 98 70) (move 96 71)

def operandWords (w : Words) : Words :=
  {w with accumulator := [], left := w.accumulator, power := [], right := w.power}

theorem prepareOperands_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hl : w.left = []) (hr : w.right = []) :
    Eval prepareOperands (6 * w.accumulator.length + 6 * w.power.length + 12)
      (state regs frame w) (state (readRegs regs 0 1 none) frame (operandWords w)) := by
  have h1 := move_eval (state regs frame w) 98 70 (by decide) (by decide) (by decide)
    (by simp [state]) (by simpa [state] using hl)
  let w1 : Words := {w with accumulator := [], left := w.accumulator}
  have e1 : moved (state regs frame w) 98 70 =
      state (readRegs regs 0 1 none) frame w1 := by
    simp only [moved, state, store_accumulator, update_store_accumulator,
      update_store_left, w1]
  rw [e1] at h1
  have h2 := move_eval (state (readRegs regs 0 1 none) frame w1) 96 71
    (by decide) (by decide) (by decide) (by simp [state])
    (by simpa [state, w1] using hr)
  have e2 : moved (state (readRegs regs 0 1 none) frame w1) 96 71 =
      state (readRegs regs 0 1 none) frame (operandWords w) := by
    simp only [moved, state, store_power, update_store_power, update_store_right,
      readRegs_reset, w1, operandWords]
  rw [e2] at h2
  have hh := h1.seq h2
  convert hh using 1
  · simp only [state, store_accumulator, store_power, w1]
    omega

abbrev finishOperands : Cmd 8 110 := .seq (move 72 98) (.seq (clear 94) (clear 95))

def finishedWords (w : Words) : Words :=
  {w with result := [], accumulator := w.result, node := [], negative := []}

theorem finishOperands_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (ha : w.accumulator = []) :
    Eval finishOperands
      (6 * w.result.length + 2 * w.node.length + 2 * w.negative.length + 12)
      (state regs frame w) (state (readRegs regs 0 1 none) frame (finishedWords w)) := by
  have h1 := move_eval (state regs frame w) 72 98 (by decide) (by decide) (by decide)
    (by simp [state]) (by simpa [state] using ha)
  let w1 : Words := {w with result := [], accumulator := w.result}
  have e1 : moved (state regs frame w) 72 98 =
      state (readRegs regs 0 1 none) frame w1 := by
    simp only [moved, state, store_result, update_store_result,
      update_store_accumulator, w1]
  rw [e1] at h1
  have h2 := clear_eval (state (readRegs regs 0 1 none) frame w1) 94
  let w2 : Words := {w1 with node := []}
  have e2 : (⟨readRegs (readRegs regs 0 1 none) 0 1 none,
      Function.update (store frame w1) 94 []⟩ : Data) =
      state (readRegs regs 0 1 none) frame w2 := by
    simp only [readRegs_reset, update_store_node, state, w2]
  change Eval _ _ _ (⟨readRegs (readRegs regs 0 1 none) 0 1 none,
    Function.update (store frame w1) 94 []⟩ : Data) at h2
  rw [e2] at h2
  have h3 := clear_eval (state (readRegs regs 0 1 none) frame w2) 95
  have e3 : (⟨readRegs (readRegs regs 0 1 none) 0 1 none,
      Function.update (store frame w2) 95 []⟩ : Data) =
      state (readRegs regs 0 1 none) frame (finishedWords w) := by
    simp only [readRegs_reset, update_store_negative, state, w2, w1, finishedWords]
  change Eval _ _ _ (⟨readRegs (readRegs regs 0 1 none) 0 1 none,
    Function.update (store frame w2) 95 []⟩ : Data) at h3
  rw [e3] at h3
  have hh := h1.seq (h2.seq h3)
  convert hh using 1
  · simp only [state, store_result, store_node, store_negative, w1, w2]
    omega

theorem seq_assoc {first second third : Cmd 8 110} {n : ℕ} {a b : Data}
    (h : Eval (.seq (.seq first second) third) n a b) :
    Eval (.seq first (.seq second third)) n a b := by
  cases h with
  | seq h12 h3 =>
    cases h12 with
    | seq h1 h2 => simpa only [Nat.add_assoc] using h1.seq (h2.seq h3)

def takenWords (w : Words) (bits rest : List Bool) : Words :=
  {w with stream := rest, node := bits}

def poweredWords (w : Words) (bits rest negative powered : List Bool) : Words :=
  {takenWords w bits rest with negative := negative, power := powered}

def advancedWords (w : Words) (rest result : List Bool) : Words :=
  {w with
    stream := rest
    accumulator := result
    node := []
    negative := []
    power := []
    left := []
    right := []
    result := []}

/-- Exact composition of all stream, scalar-call, move, and cleanup stages. -/
theorem iteration_eval (negate power multiply : Cmd 8 110)
    (regs rn rp rm : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (bits rest negative powered result : List Bool)
    (nn np nm : ℕ) (hs : w.stream = bits ++ rest)
    (hw : w.blockWidth.length = bits.length) (hn : w.node = [])
    (hl : w.left = []) (hr : w.right = [])
    (hneg : Eval negate nn
      (state (readRegs regs 0 1 none) frame (takenWords w bits rest))
      (state rn frame {takenWords w bits rest with negative := negative}))
    (hpow : Eval power np
      (state rn frame {takenWords w bits rest with negative := negative})
      (state rp frame (poweredWords w bits rest negative powered)))
    (hmul : Eval multiply nm
      (state (readRegs rp 0 1 none) frame
        (operandWords (poweredWords w bits rest negative powered)))
      (state rm frame
        {operandWords (poweredWords w bits rest negative powered) with
          left := [], right := [], result := result})) :
    Eval (iteration negate power multiply)
      (16 * bits.length + 6 * w.accumulator.length + 6 * powered.length +
        6 * result.length + 2 * negative.length + nn + np + nm + 35)
      (state regs frame w)
      (state (readRegs rm 0 1 none) frame (advancedWords w rest result)) := by
  have ht := takeNode_eval regs frame w bits rest hs hw hn
  have hp := prepareOperands_eval rp frame (poweredWords w bits rest negative powered)
    (by simpa [poweredWords, takenWords] using hl)
    (by simpa [poweredWords, takenWords] using hr)
  have hf := finishOperands_eval rm frame
    {operandWords (poweredWords w bits rest negative powered) with
      left := [], right := [], result := result} rfl
  have hh := ht.seq (hneg.seq (hpow.seq (seq_assoc (hp.seq (hmul.seq hf)))))
  convert hh using 1
  · simp only [operandWords, poweredWords, takenWords]
    omega
  all_goals rfl

theorem peekNodes_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) :
    Eval peekNodes 1 (state regs frame w)
      (state (readRegs regs 0 1 w.stream.head?) frame w) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.peek 99 0 1) (state regs frame w))
  simpa only [peekNodes, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
    state, store_stream] using h

def readyWords {C : Type*} (encode : C → List Bool) (base : Words)
    (cs : List C) (a : C) : Words :=
  {base with
    stream := cs.flatMap encode
    accumulator := encode a
    node := []
    negative := []
    power := []
    left := []
    right := []
    result := []}

def initialWords {C : Type*} (encode : C → List Bool) (base : Words)
    (cs : List C) : Words :=
  {base with
    stream := cs.flatMap encode
    accumulator := []
    node := []
    negative := []
    power := []
    left := []
    right := []
    result := []}

/-- The loop allows arithmetic services to return any correctly decoded word.
It therefore does not add a choice-based implementation of exponentiation. -/
theorem loop_eval {C R : Type*} [Monoid R] (encode : C → List Bool)
    (value factor : C → R) (base : Words) (frame : Fin 110 → List Bool)
    (body : Cmd 8 110) (K : ℕ) (hne : ∀ c, encode c ≠ [])
    (hstep : ∀ regs cs a c, ∃ n ≤ K, ∃ rf b,
      Eval body n (state regs frame (readyWords encode base (c :: cs) a))
        (state rf frame (readyWords encode base cs b)) ∧
      value b = value a * factor c)
    (cs : List C) (a : C) (regs : Fin 8 → Bool) :
    ∃ n ≤ cs.length * (K + 2) + 1, ∃ rf b,
      Eval (.while 1 (.seq body peekNodes)) n
        (state (readRegs regs 0 1 (cs.flatMap encode).head?) frame
          (readyWords encode base cs a))
        (state rf frame (readyWords encode base [] b)) ∧
      value b = value a * (cs.map factor).prod := by
  induction cs generalizing a regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, a, ?_, by simp⟩
      exact Eval.while_false (by simp [state, readRegs])
  | cons c cs ih =>
      let r0 := readRegs regs 0 1 ((c :: cs).flatMap encode).head?
      obtain ⟨n, hn, r1, b1, he, hv⟩ := hstep r0 cs a c
      have hp := peekNodes_eval r1 frame (readyWords encode base cs b1)
      obtain ⟨m, hm, rf, b, ht, hb⟩ := ih b1 r1
      have hg : (state r0 frame (readyWords encode base (c :: cs) a)).regs 1 = true := by
        cases hc : encode c with
        | nil => exact False.elim (hne c hc)
        | cons bit bits => simp [r0, state, readRegs, hc]
      have hh := Eval.while_true hg (he.seq hp) ht
      refine ⟨n + 1 + m + 1, ?_, rf, b, hh, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · rw [hb, hv]
        simp only [List.map_cons, List.prod_cons, mul_assoc]

theorem command_eval {C R : Type*} [Monoid R] (encode : C → List Bool)
    (value factor : C → R) (base : Words) (frame : Fin 110 → List Bool)
    (negate power multiply : Cmd 8 110) (K : ℕ) (hne : ∀ c, encode c ≠ [])
    (unit : C) (hu : value unit = 1) (hunit : base.unit = encode unit)
    (hstep : ∀ regs cs a c, ∃ n ≤ K, ∃ rf b,
      Eval (iteration negate power multiply) n
        (state regs frame (readyWords encode base (c :: cs) a))
        (state rf frame (readyWords encode base cs b)) ∧
      value b = value a * factor c)
    (cs : List C) (regs : Fin 8 → Bool) :
    ∃ n ≤ 7 * (encode unit).length + cs.length * (K + 2) + 7, ∃ rf b,
      Eval (command negate power multiply) n
        (state regs frame (initialWords encode base cs))
        (state rf frame (readyWords encode base [] b)) ∧
      value b = (cs.map factor).prod := by
  have hc := copy_eval (state regs frame (initialWords encode base cs)) 93 98 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have ec : afterCopy (state regs frame (initialWords encode base cs)) 93 98 0 1 =
      state (readRegs regs 0 1 none) frame (readyWords encode base cs unit) := by
    simp only [afterCopy, state, copyStacks, store_unit, store_accumulator,
      initialWords, hunit, List.append_nil, update_store_accumulator, readyWords]
  rw [ec] at hc
  have hp := peekNodes_eval (readRegs regs 0 1 none) frame (readyWords encode base cs unit)
  obtain ⟨m, hm, rf, b, hl, hv⟩ := loop_eval encode value factor base frame
    (iteration negate power multiply) K hne hstep cs unit (readRegs regs 0 1 none)
  have hh := hc.seq (hp.seq hl)
  refine ⟨7 * (encode unit).length + 5 + (1 + m), by omega, rf, b, ?_, ?_⟩
  · simpa only [command, state, store_unit, initialWords, hunit] using hh
  · simpa only [hu, one_mul] using hv

@[simp] theorem store_processed (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 100 = frame 100 := rfl

@[simp] theorem store_remaining (frame : Fin 110 → List Bool) (w : Words) :
    store frame w 101 = frame 101 := rfl

/-- The outer traversal stores processed and remaining nodes on 100 and 101.
These two actual copies form the excluded-node stream without a division or
an assumption that any node value is nonzero. -/
abbrev prepareStream : Cmd 8 110 :=
  .seq (.call (copyProgram 100 99 0 (0 : Fin 8) 1))
    (.call (copyProgram 101 99 0 (0 : Fin 8) 1))

theorem prepareStream_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hs : w.stream = []) :
    Eval prepareStream (7 * (frame 100).length + 7 * (frame 101).length + 10)
      (state regs frame w)
      (state (readRegs regs 0 1 none) frame {w with stream := frame 101 ++ frame 100}) := by
  have h1 := copy_eval (state regs frame w) 100 99 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have e1 : afterCopy (state regs frame w) 100 99 0 1 =
      state (readRegs regs 0 1 none) frame {w with stream := frame 100} := by
    simp only [afterCopy, state, copyStacks, store_processed, store_stream, hs,
      List.append_nil, update_store_stream]
  rw [e1] at h1
  have h2 := copy_eval (state (readRegs regs 0 1 none) frame {w with stream := frame 100})
    101 99 0 0 1 (by decide) (by decide) (by decide) (by decide) (by simp [state])
  have e2 : afterCopy
      (state (readRegs regs 0 1 none) frame {w with stream := frame 100}) 101 99 0 1 =
      state (readRegs regs 0 1 none) frame {w with stream := frame 101 ++ frame 100} := by
    simp only [afterCopy, state, copyStacks, store_remaining, store_stream,
      update_store_stream, readRegs_reset]
  rw [e2] at h2
  have hh := h1.seq h2
  convert hh using 1
  simp only [state, store_processed, store_remaining]
  omega

theorem update_store_blockWidth (frame : Fin 110 → List Bool) (w : Words) (bits : List Bool) :
    Function.update (store frame w) 104 bits = store frame {w with blockWidth := bits} := by
  funext j
  by_cases hj : j = 104
  · subst j; simp
  · simp [store, nativeStore, hj]

/-- Materialize the 4B parsing counter from the B-width runtime word. -/
abbrev initializeWidth : Cmd 8 110 :=
  .seq (.call (copyProgram 74 107 108 (0 : Fin 8) 1))
    (.call (zeroFillProgram 107 104 (0 : Fin 8) 1))

theorem initializeWidth_eval (regs : Fin 8 → Bool) (frame : Fin 110 → List Bool)
    (w : Words) (hw : w.blockWidth = []) :
    Eval initializeWidth (14 * w.width.length + 8) (state regs frame w)
      (state (readRegs regs 0 1 none) frame
        {w with blockWidth := List.replicate (4 * w.width.length) false}) := by
  let d0 := state regs frame w
  let d1 := afterCopy d0 74 107 0 1
  have h1 := copy_eval d0 74 107 108 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [d0, state])
  have h2 := zeroFill_eval 107 104 0 1 (by decide) (by decide) d1
  have hlen : (d1.stacks 107).length = w.width.length := by
    simp [d1, d0, afterCopy, copyStacks, state]
  have hrestore : Function.update (store frame w) 107 [] = store frame w := by
    funext j
    by_cases hj : j = 107
    · subst j; simp
    · simp only [Function.update_noteq hj]
  have he : (⟨readRegs d1.regs 0 1 none,
      zeroFillStacks 107 104 (d1.stacks 107).length d1.stacks⟩ : Data) =
      state (readRegs regs 0 1 none) frame
        {w with blockWidth := List.replicate (4 * w.width.length) false} := by
    apply state_ext
    · simp only [d1, d0, afterCopy, state, readRegs_reset]
    · simp only [zeroFillStacks, d1, d0, afterCopy, state, copyStacks,
        store_width, store_takeCounter, List.append_nil, Function.update_idem,
        Function.update_self,
        Function.update_noteq (by decide : (104 : Fin 110) ≠ 107), store_blockWidth,
        hw, hrestore, update_store_blockWidth]
  rw [he] at h2
  have hh := h1.seq h2
  convert hh using 1
  simp only [d0, state, store_width, hlen]
  omega

end SubexponentialSAT.SubexpCRTCofactorLoop

end OAI.Algorithms
