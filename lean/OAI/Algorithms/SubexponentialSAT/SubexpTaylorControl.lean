import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHornerControl

namespace OAI.Algorithms

/-! Fixed streaming control for the affine polynomial step
`b + (X + theta) * Q`.  The arithmetic service operates on one encoded
coefficient at a time; all scanning and loop control is proved here. -/

namespace SubexponentialSAT.SubexpTaylorControl

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl

abbrev takeCurrent : Cmd 8 87 := takeWord 81 82 83 77 72 0 1
abbrev saveCurrent : Cmd 8 87 := .call (StackRoutines.copyProgram 72 83 0 (0 : Fin 8) 1)
abbrev packCurrent : Cmd 8 87 := .call (StackRoutines.transferProgram 72 79 (0 : Fin 8) 1)
abbrev restorePrevious : Cmd 8 87 :=
  .seq (.call (StackRoutines.transferProgram 83 0 (0 : Fin 8) 1))
    (.call (StackRoutines.transferProgram 0 80 (0 : Fin 8) 1))
abbrev finish : Cmd 8 87 :=
  .seq (.call (StackRoutines.transferProgram 80 79 (0 : Fin 8) 1))
    (.call (StackRoutines.transferProgram 79 77 (0 : Fin 8) 1))
abbrev guard : Cmd 8 87 := .base (.atom (.peek 77 0 1))
abbrev iteration (arithmetic : Cmd 8 87) : Cmd 8 87 :=
  .seq takeCurrent (.seq saveCurrent (.seq arithmetic (.seq packCurrent restorePrevious)))
abbrev tail (arithmetic : Cmd 8 87) : Cmd 8 87 :=
  .seq (.while 1 (.seq (iteration arithmetic) guard)) finish
abbrev command (arithmetic : Cmd 8 87) : Cmd 8 87 := .seq guard (tail arithmetic)
abbrev program (arithmetic : Cmd 8 87) : Program 8 87 (size (command arithmetic) + 1) :=
  compiled (command arithmetic) 77 77

theorem takeCurrent_eval (regs : Fin 8 → Bool) (w : Words) (bits rest : List Bool)
    (hs : w.stream = bits ++ rest) (hw : w.blockWidth.length = bits.length)
    (ha : w.accumulator = []) (hi : w.index = []) (ht : w.scratch = []) :
    Eval takeCurrent (14 * bits.length + 11) (state regs w)
      (state (readRegs regs 0 1 none) {w with stream := rest, accumulator := bits}) := by
  have h := takeWord_eval (state regs w) 81 82 83 77 72 0 1
    (by decide) (by decide) bits rest
    (by simpa [state, store] using hs) (by simpa [state, store] using hi)
    (by simpa [state, store] using ht) (by simpa [state, store] using hw)
  convert h using 1
  apply state_ext
  · rfl
  · funext i
    by_cases h77 : i = 77 <;> by_cases h72 : i = 72 <;>
      simp [afterTake, state, store, h77, h72, ha]

theorem saveCurrent_eval (regs : Fin 8 → Bool) (w : Words)
    (ht : w.scratch = []) (hwork : w.work = []) :
    Eval saveCurrent (7 * w.accumulator.length + 5) (state regs w)
      (state (readRegs regs 0 1 none) {w with scratch := w.accumulator}) := by
  have h := copy_eval (state regs w) 72 83 0 0 1
    (by decide) (by decide) (by decide) (by decide) (by simpa [state, store] using hwork)
  have hlen : ((state regs w).stacks (72 : Fin 87)).length = w.accumulator.length := rfl
  rw [hlen] at h
  convert h using 1
  apply state_ext
  · rfl
  · funext i
    by_cases h83 : i = 83 <;>
      simp [afterCopy, StackRoutines.copyStacks, state, store, h83, ht]

theorem packCurrent_eval (regs : Fin 8 → Bool) (w : Words) :
    Eval packCurrent (3 * w.accumulator.length + 3) (state regs w)
      (state (readRegs regs 0 1 none)
        {w with accumulator := [], shape := w.accumulator.reverse ++ w.shape}) := by
  have h := transfer_eval (state regs w) 72 79 0 1 (by decide) (by decide)
  have hlen : ((state regs w).stacks (72 : Fin 87)).length = w.accumulator.length := rfl
  rw [hlen] at h
  convert h using 1
  apply state_ext
  · rfl
  · funext i
    by_cases h72 : i = 72 <;> by_cases h79 : i = 79 <;>
      simp [afterTransfer, StackRoutines.transferStacks, state, store, h72, h79]

theorem restorePrevious_eval (regs : Fin 8 → Bool) (w : Words)
    (hwork : w.work = []) (hc : w.coefficient = []) :
    Eval restorePrevious (6 * w.scratch.length + 6) (state regs w)
      (state (readRegs regs 0 1 none) {w with scratch := [], coefficient := w.scratch}) := by
  let w1 := {w with scratch := [], work := w.scratch.reverse}
  have h1 := transfer_eval (state regs w) 83 0 0 1 (by decide) (by decide)
  have e1 : afterTransfer (state regs w) 83 0 0 1 =
      state (readRegs regs 0 1 none) w1 := by
    apply state_ext
    · rfl
    · funext i
      by_cases h0 : i = 0 <;> by_cases h83 : i = 83 <;>
        simp [afterTransfer, StackRoutines.transferStacks, state, store, w1, h0, h83, hwork]
  rw [e1] at h1
  have h2 := transfer_eval (state (readRegs regs 0 1 none) w1) 0 80 0 1
    (by decide) (by decide)
  have e2 : afterTransfer (state (readRegs regs 0 1 none) w1) 0 80 0 1 =
      state (readRegs regs 0 1 none) {w with scratch := [], coefficient := w.scratch} := by
    apply state_ext
    · simp [afterTransfer, state, StackRoutines.readRegs_reset]
    · funext i
      by_cases h0 : i = 0 <;> by_cases h80 : i = 80 <;>
        simp [afterTransfer, StackRoutines.transferStacks, state, store, w1, h0, h80,
          hwork, hc]
  rw [e2] at h2
  convert h1.seq h2 using 1
  simp [w1, state, store]
  omega

theorem finish_eval (regs : Fin 8 → Bool) (w : Words) (hs : w.stream = []) :
    Eval finish (6 * w.coefficient.length + 3 * w.shape.length + 6) (state regs w)
      (state (readRegs regs 0 1 none)
        {w with coefficient := [], shape := [], stream := w.shape.reverse ++ w.coefficient}) := by
  let w1 := {w with coefficient := [], shape := w.coefficient.reverse ++ w.shape}
  have h1 := transfer_eval (state regs w) 80 79 0 1 (by decide) (by decide)
  have e1 : afterTransfer (state regs w) 80 79 0 1 =
      state (readRegs regs 0 1 none) w1 := by
    apply state_ext
    · rfl
    · funext i
      by_cases h79 : i = 79 <;> by_cases h80 : i = 80 <;>
        simp [afterTransfer, StackRoutines.transferStacks, state, store, w1, h79, h80]
  rw [e1] at h1
  have h2 := transfer_eval (state (readRegs regs 0 1 none) w1) 79 77 0 1
    (by decide) (by decide)
  have e2 : afterTransfer (state (readRegs regs 0 1 none) w1) 79 77 0 1 =
      state (readRegs regs 0 1 none)
        {w with coefficient := [], shape := [], stream := w.shape.reverse ++ w.coefficient} := by
    apply state_ext
    · simp [afterTransfer, state, StackRoutines.readRegs_reset]
    · funext i
      by_cases h77 : i = 77 <;> by_cases h79 : i = 79 <;>
        simp [afterTransfer, StackRoutines.transferStacks, state, store, w1, h77, h79, hs]
  rw [e2] at h2
  convert h1.seq h2 using 1
  simp [w1, state, store]
  omega

theorem guard_eval (regs : Fin 8 → Bool) (w : Words) :
    Eval guard 1 (state regs w) (state (readRegs regs 0 1 w.stream.head?) w) := by
  exact .base (.atom _ _)

def encodeList {C : Type*} (encode : C → List Bool) (xs : List C) : List Bool := xs.flatMap encode

def ready {C : Type*} (encode : C → List Bool) (base : Words)
    (xs : List C) (previous : C) (packed : List Bool) : Words :=
  {base with
    stream := encodeList encode xs
    accumulator := []
    coefficient := encode previous
    shape := packed
    work := []
    left := []
    right := []
    index := []
    scratch := []}

def done (base : Words) (output : List Bool) : Words :=
  {base with
    stream := output
    accumulator := []
    coefficient := []
    shape := []
    work := []
    left := []
    right := []
    index := []
    scratch := []}

def sweep {C : Type*} (step : C → C → C) : C → List C → List C
  | b, [] => [b]
  | b, a :: xs => step a b :: sweep step a xs

@[simp] theorem sweep_length {C : Type*} (step : C → C → C) (b : C) (xs : List C) :
    (sweep step b xs).length = xs.length + 1 := by
  induction xs generalizing b with
  | nil => rfl
  | cons a xs ih => simp [sweep, ih]

section Service

variable {C : Type*} (encode : C → List Bool) (B : ℕ)
  (hencode : ∀ a, (encode a).length = B)
  (base : Words) (hwidth : base.blockWidth.length = B)
  (arithmetic : Cmd 8 87) (step : C → C → C) (K : ℕ)
  (harithmetic : ∀ regs (w : Words) a b,
    w.modulus = base.modulus → w.width = base.width →
    w.reduction = base.reduction → w.point = base.point →
    w.accumulator = encode a → w.coefficient = encode b →
    w.work = [] → w.left = [] → w.right = [] →
    ∃ n ≤ K, ∃ regs', Eval arithmetic n (state regs w)
      (state regs' {w with accumulator := encode (step a b), coefficient := []}))

include hencode hwidth harithmetic

theorem iteration_eval (regs : Fin 8 → Bool) (a b : C) (xs : List C) (packed : List Bool) :
    ∃ n ≤ K + 30 * B + 25, ∃ regs',
      Eval (iteration arithmetic) n (state regs (ready encode base (a :: xs) b packed))
        (state regs' (ready encode base xs a ((encode (step a b)).reverse ++ packed))) := by
  let w := ready encode base (a :: xs) b packed
  let w1 := {w with stream := encodeList encode xs, accumulator := encode a}
  let w2 := {w1 with scratch := encode a}
  let w3 := {w2 with accumulator := encode (step a b), coefficient := []}
  let w4 := {w3 with accumulator := [], shape := (encode (step a b)).reverse ++ packed}
  have h1 := takeCurrent_eval regs w (encode a) (encodeList encode xs) rfl
    (by simpa [w, ready] using hwidth.trans (hencode a).symm) rfl rfl rfl
  have h2 := saveCurrent_eval (readRegs regs 0 1 none) w1 rfl rfl
  obtain ⟨n, hn, rr, h3⟩ := harithmetic (readRegs regs 0 1 none) w2 a b
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h4 := packCurrent_eval rr w3
  have h5 := restorePrevious_eval (readRegs rr 0 1 none) w4 rfl rfl
  simp only [StackRoutines.readRegs_reset] at h2 h5
  refine ⟨14 * (encode a).length + 11 +
      (7 * (encode a).length + 5 + (n +
      (3 * (encode (step a b)).length + 3 + (6 * (encode a).length + 6)))), ?_,
    readRegs rr 0 1 none, ?_⟩
  · simp only [hencode]; omega
  · simpa only [iteration, w, w1, w2, w3, w4, ready, StackRoutines.readRegs_reset]
      using h1.seq (h2.seq (h3.seq (h4.seq h5)))

end Service

end SubexponentialSAT.SubexpTaylorControl

end OAI.Algorithms
