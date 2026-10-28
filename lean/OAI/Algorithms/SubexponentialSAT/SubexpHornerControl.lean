import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Fixed streaming control for dense Horner evaluation. Arithmetic is a
separate actual command, instantiated by the flat quartic machine module. -/

namespace SubexponentialSAT.SubexpHornerControl

open BitProgram StructuredCalls SubexpScanPrimitives

structure Words where
  modulus : List Bool
  width : List Bool
  reduction : List Bool
  stream : List Bool
  point : List Bool
  shape : List Bool
  accumulator : List Bool
  coefficient : List Bool := []
  blockWidth : List Bool
  left : List Bool := []
  right : List Bool := []
  work : List Bool := []
  index : List Bool := []
  scratch : List Bool := []

def store (w : Words) (i : Fin 87) : List Bool :=
  if i = 0 then w.work else
  if i = 66 then w.modulus else
  if i = 70 then w.left else
  if i = 71 then w.right else
  if i = 72 then w.accumulator else
  if i = 73 then w.reduction else
  if i = 74 then w.width else
  if i = 77 then w.stream else
  if i = 78 then w.point else
  if i = 79 then w.shape else
  if i = 80 then w.coefficient else
  if i = 81 then w.blockWidth else
  if i = 82 then w.index else
  if i = 83 then w.scratch else []

def state (regs : Fin 8 → Bool) (w : Words) : State 8 87 := ⟨regs, store w⟩

abbrev takeCoefficient : Cmd 8 87 :=
  .seq (takeWord 81 82 83 77 80 0 1)
    (.call (StackRoutines.reverseProgram 80 0 1 (0 : Fin 8) 1))

theorem takeCoefficient_eval (regs : Fin 8 → Bool) (w : Words) (bits rest : List Bool)
    (hs : w.stream = bits.reverse ++ rest) (hw : w.blockWidth.length = bits.length)
    (hc : w.coefficient = []) (hi : w.index = []) (ht : w.scratch = []) (hwork : w.work = []) :
    Eval takeCoefficient (23 * bits.length + 18) (state regs w)
      (state (readRegs regs 0 1 none) {w with stream := rest, coefficient := bits}) := by
  have htake := takeWord_eval (state regs w) 81 82 83 77 80 0 1
    (by decide) (by decide) bits.reverse rest
    (by simpa [state, store] using hs) (by simpa [state, store] using hi)
    (by simpa [state, store] using ht) (by simpa [state, store] using hw)
  let mid := state (readRegs regs 0 1 none) {w with stream := rest, coefficient := bits.reverse}
  have hm : afterTake (state regs w) 77 80 0 1 bits.reverse rest = mid := by
    apply state_ext
    · rfl
    · funext i
      by_cases h77 : i = 77 <;> by_cases h80 : i = 80 <;>
        simp [afterTake, state, store, mid, h77, h80, hc]
  rw [hm] at htake
  have hrev := reverse_eval mid 80 0 1 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [mid, state, store, hwork]) (by simp [mid, state, store])
  have hr : afterReverse mid 80 0 1 =
      state (readRegs regs 0 1 none) {w with stream := rest, coefficient := bits} := by
    apply state_ext
    · simp [afterReverse, mid, state, StackRoutines.readRegs_reset]
    · funext i
      by_cases h80 : i = 80 <;>
        simp [afterReverse, StackRoutines.reverseStacks, mid, state, store, h80]
  rw [hr] at hrev
  have hh := htake.seq hrev
  convert hh using 1
  simp [ mid, state, store, Nat.add_assoc]
  omega

abbrev prepareMultiply : Cmd 8 87 :=
  .seq (.call (StackRoutines.transferProgram 72 0 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.transferProgram 0 70 (0 : Fin 8) 1))
      (.call (StackRoutines.copyProgram 78 71 1 (0 : Fin 8) 1)))

theorem prepareMultiply_eval (regs : Fin 8 → Bool) (w : Words)
    (hwork : w.work = []) (hl : w.left = []) (hr : w.right = []) :
    Eval prepareMultiply (6 * w.accumulator.length + 7 * w.point.length + 11)
      (state regs w)
      (state (readRegs regs 0 1 none)
        {w with accumulator := [], left := w.accumulator, right := w.point}) := by
  let d0 := state regs w
  let d1 := state (readRegs regs 0 1 none)
    {w with accumulator := [], work := w.accumulator.reverse}
  let d2 := state (readRegs regs 0 1 none)
    {w with accumulator := [], left := w.accumulator}
  have h1 := transfer_eval d0 72 0 0 1 (by decide) (by decide)
  have e1 : afterTransfer d0 72 0 0 1 = d1 := by
    apply state_ext
    · rfl
    · funext i
      by_cases h0 : i = 0 <;> by_cases h72 : i = 72 <;>
        simp [afterTransfer, StackRoutines.transferStacks, d0, d1, state, store, h0, h72, hwork]
  rw [e1] at h1
  have h2 := transfer_eval d1 0 70 0 1 (by decide) (by decide)
  have e2 : afterTransfer d1 0 70 0 1 = d2 := by
    apply state_ext
    · simp [afterTransfer, d1, d2, state, StackRoutines.readRegs_reset]
    · funext i
      by_cases h0 : i = 0 <;> by_cases h70 : i = 70 <;>
        simp [afterTransfer, StackRoutines.transferStacks, d1, d2, state, store, h0, h70,
          hwork, hl]
  rw [e2] at h2
  have h3 := copy_eval d2 78 71 1 0 1 (by decide) (by decide) (by decide) (by decide)
    (by simp [d2, state, store])
  have e3 : afterCopy d2 78 71 0 1 =
      state (readRegs regs 0 1 none)
        {w with accumulator := [], left := w.accumulator, right := w.point} := by
    apply state_ext
    · simp [afterCopy, d2, state, StackRoutines.readRegs_reset]
    · funext i
      by_cases h71 : i = 71 <;>
        simp [afterCopy, StackRoutines.copyStacks, d2, state, store, h71, hr]
  rw [e3] at h3
  have hh := h1.seq (h2.seq h3)
  convert hh using 1
  simp [ d0, d1, d2, state, store, Nat.add_assoc]
  omega

abbrev popShape : Cmd 8 87 := .base (.atom (.pop 79 0 1))

theorem popShape_eval (regs : Fin 8 → Bool) (w : Words) :
    Eval popShape 1 (state regs w)
      (state (readRegs regs 0 1 w.shape.head?) {w with shape := w.shape.tail}) := by
  have h := Eval.base (StructuredProgram.Eval.atom (.pop 79 0 1) (state regs w))
  convert h using 1
  apply state_ext
  · rfl
  · funext i
    by_cases h79 : i = 79 <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        state, store, h79]

abbrev command (iteration : Cmd 8 87) : Cmd 8 87 :=
  .seq popShape (.while 1 (.seq iteration popShape))

def backward {C : Type*} (encode : C → List Bool) (cs : List C) : List Bool :=
  cs.flatMap (fun c => (encode c).reverse)

def readyWords {C : Type*} (encode : C → List Bool) (base : Words)
    (cs : List C) (a : C) : Words :=
  { base with
    stream := backward encode cs
    shape := List.replicate cs.length false
    accumulator := encode a
    coefficient := []
    left := []
    right := []
    work := []
    index := []
    scratch := [] }

abbrev fold {C : Type*} (step : C → C → C) : List C → C → C
  | [], a => a
  | c :: cs, a => fold step cs (step a c)

theorem loop_eval {C : Type*} (encode : C → List Bool) (base : Words)
    (iteration : Cmd 8 87) (step : C → C → C) (K : ℕ)
    (hstep : ∀ regs cs a c,
      ∃ n ≤ K, ∃ regs', Eval iteration n
        (state regs {(readyWords encode base (c :: cs) a) with shape := List.replicate cs.length false})
        (state regs' (readyWords encode base cs (step a c))))
    (cs : List C) (a : C) (regs : Fin 8 → Bool) :
    ∃ n ≤ cs.length * (K + 2) + 1, ∃ regs',
      Eval (.while 1 (.seq iteration popShape)) n
        (state (readRegs regs 0 1 (List.replicate cs.length false).head?)
          {(readyWords encode base cs a) with shape := (List.replicate cs.length false).tail})
        (state regs' (readyWords encode base [] (fold step cs a))) := by
  induction cs generalizing a regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
      exact Eval.while_false (by simp [state, readRegs])
  | cons c cs ih =>
      obtain ⟨n, hn, r1, h1⟩ := hstep (readRegs regs 0 1 (some false)) cs a c
      have hp := popShape_eval r1 (readyWords encode base cs (step a c))
      obtain ⟨m, hm, r2, h2⟩ := ih (step a c) r1
      have hh := Eval.while_true (by simp [state, readRegs]) (h1.seq hp) h2
      refine ⟨n + 1 + m + 1, ?_, r2, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
      · simpa [readyWords, fold, List.replicate_succ, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hh

theorem command_eval {C : Type*} (encode : C → List Bool) (base : Words)
    (iteration : Cmd 8 87) (step : C → C → C) (K : ℕ)
    (hstep : ∀ regs cs a c,
      ∃ n ≤ K, ∃ regs', Eval iteration n
        (state regs {(readyWords encode base (c :: cs) a) with shape := List.replicate cs.length false})
        (state regs' (readyWords encode base cs (step a c))))
    (cs : List C) (a : C) (regs : Fin 8 → Bool) :
    ∃ n ≤ cs.length * (K + 2) + 2, ∃ regs',
      Eval (command iteration) n (state regs (readyWords encode base cs a))
        (state regs' (readyWords encode base [] (fold step cs a))) := by
  have hp := popShape_eval regs (readyWords encode base cs a)
  obtain ⟨n, hn, rf, hr⟩ := loop_eval encode base iteration step K hstep cs a regs
  exact ⟨1 + n, by omega, rf, hp.seq hr⟩

end SubexponentialSAT.SubexpHornerControl

end OAI.Algorithms
