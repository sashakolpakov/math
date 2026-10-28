import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpKeyPadProgram
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! Fixed-control conversion of a flat coefficient stream into an ordered
list of framed coefficients. Runtime counters determine the coefficient
width and requested count. Missing high coefficients are actually read as
zero by the existing padded-reader program. -/

namespace SubexponentialSAT.SubexpTaylorFrames

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpExponentProgram

structure Words where
  input : List Bool
  width : List Bool
  todo : List Bool
  counter : List Bool := []
  payload : List Bool := []
  record : List Bool := []
  packed : List Bool := []
  scratch : List Bool := []
  output : List Bool := []

def store (w : Words) : Fin 9 → List Bool :=
  ![w.input, w.width, w.counter, w.todo, w.payload, w.record,
    w.packed, w.scratch, w.output]

def state (regs : Fin 5 → Bool) (w : Words) : State 5 9 := ⟨regs, store w⟩

def padRegs : Fin 2 → Fin 5 := ![0, 1]
def padStacks : Fin 3 → Fin 9 := ![0, 2, 4]
def writerStacks : Fin 6 → Fin 9 := ![0, 4, 1, 5, 2, 7]

theorem padRegs_injective : Function.Injective padRegs := by decide
theorem padStacks_injective : Function.Injective padStacks := by decide
theorem writerStacks_injective : Function.Injective writerStacks := by decide

abbrev paddedRead : Cmd 5 9 :=
  .call (ProgramLinking.liftProgram SubexpKeyPadProgram.program padRegs padStacks)

abbrev writeRecord : Cmd 5 9 :=
  .call (ProgramLinking.liftProgram (SubexpArgumentProgram.writer true) id writerStacks)

def recordBytes (bits : List Bool) : List Bool := true :: Encoding.frame bits

abbrev one : Cmd 5 9 :=
  .seq (.call (StackRoutines.copyProgram 1 2 7 (0 : Fin 5) 1))
    (.seq paddedRead (.seq writeRecord
      (.call (StackRoutines.transferProgram 5 6 (0 : Fin 5) 1))))

abbrev guard : Cmd 5 9 := .base (.atom (.peek 3 0 1))
abbrev popCount : Cmd 5 9 := .base (.atom (.pop 3 0 1))
abbrev loop : Cmd 5 9 := .while 1 (.seq popCount (.seq one guard))
abbrev finish : Cmd 5 9 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 6 0)))
      (.call (StackRoutines.transferProgram 6 8 (0 : Fin 5) 1)))
abbrev command : Cmd 5 9 := .seq guard (.seq loop finish)
abbrev program : Program 5 9 (size command + 1) := compiled command 0 8

/-- The reader tests counter presence, so either bit value is a valid tick. -/
theorem pad_round (bit : Bool) (regs : Fin 2 → Bool) (input counter output : List Bool) :
    Trace SubexpKeyPadProgram.program 4
      (SubexpKeyPadProgram.cfg (some 0) regs input (bit :: counter) output)
      (SubexpKeyPadProgram.cfg (some 0) (readRegs regs 0 1 input.head?)
        input.tail counter (input.head?.getD false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, SubexpKeyPadProgram.program,
    execInstr, SubexpKeyPadProgram.cfg, SubexpKeyPadProgram.storage,
    readRegs, Function.update_apply]
  constructor <;> funext i <;> fin_cases i <;> simp

theorem pad_counter_trace (counter : List Bool) (regs : Fin 2 → Bool)
    (input output : List Bool) :
    ∃ finalRegs, Trace SubexpKeyPadProgram.program (4 * counter.length + 3)
      (SubexpKeyPadProgram.cfg (some 0) regs input counter output)
      (SubexpKeyPadProgram.cfg none finalRegs (input.drop counter.length) []
        ((padTake counter.length input).reverse ++ output)) := by
  induction counter generalizing regs input output with
  | nil => exact ⟨readRegs regs 0 1 none, by
      simpa using (SubexpKeyPadProgram.exit_trace regs input output)⟩
  | cons bit counter ih =>
      have h1 := pad_round bit regs input counter output
      obtain ⟨rr, h2⟩ := ih (readRegs regs 0 1 input.head?) input.tail
        (input.head?.getD false :: output)
      refine ⟨rr, ?_⟩
      have ht := h1.trans h2
      rw [List.drop_tail] at ht
      simp only [List.length_cons, SubexpKeyPadProgram.padTake_step,
        List.reverse_cons, List.append_assoc]
      convert ht using 1
      · omega
      · simp only [List.singleton_append]

theorem paddedRead_eval (B : ℕ) (regs : Fin 5 → Bool) (w : Words)
    (hc : w.counter.length = B) :
    ∃ regs', Eval paddedRead (4 * B + 3) (state regs w)
      (state regs' {w with
        input := w.input.drop B
        counter := []
        payload := (padTake B w.input).reverse ++ w.payload}) := by
  obtain ⟨rr, hr⟩ := pad_counter_trace w.counter (regs ∘ padRegs) w.input w.payload
  rw [hc] at hr
  let regs' : Fin 5 → Bool := fun i => if i = 0 then rr 0 else if i = 1 then rr 1 else regs i
  let a : State 2 3 := ⟨regs ∘ padRegs,
    SubexpKeyPadProgram.storage w.input w.counter w.payload⟩
  let b : State 2 3 := ⟨rr,
    SubexpKeyPadProgram.storage (w.input.drop B) [] ((padTake B w.input).reverse ++ w.payload)⟩
  have ha : embedState padRegs padStacks (state regs w) a = state regs w := by
    apply embedState_eq _ _ padRegs_injective padStacks_injective
    · intro i; rfl
    · intro i; fin_cases i <;> simp [a, state, store, padStacks, SubexpKeyPadProgram.storage ]
    · intros; rfl
    · intros; rfl
  have hb : embedState padRegs padStacks (state regs w) b =
      state regs' {w with
        input := w.input.drop B
        counter := []
        payload := (padTake B w.input).reverse ++ w.payload} := by
    apply embedState_eq _ _ padRegs_injective padStacks_injective
    · intro i; fin_cases i <;> simp [regs', state, b, padRegs]
    · intro i; fin_cases i <;> simp [state, store, b, padStacks, SubexpKeyPadProgram.storage]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [state, regs', h0, h1]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨1, h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2, h.symm⟩
      fin_cases i <;> simp_all [state, store]
  have he := eval_call_lifted SubexpKeyPadProgram.program padRegs padStacks (state regs w)
    padRegs_injective padStacks_injective (a := a) (b := b) hr
  exact ⟨regs', by simpa only [paddedRead, ha, hb] using he⟩

theorem writeRecord_eval (regs : Fin 5 → Bool) (w : Words) (bits : List Bool)
    (hp : w.payload = bits.reverse) :
    Eval writeRecord (5 * bits.length + 7) (state regs w)
      (state (SubexpArgumentProgram.finishedRegs regs)
        {w with payload := [], record := recordBytes bits ++ w.record}) := by
  let a : State 5 6 := ⟨regs, fun i => store w (writerStacks i)⟩
  have hr := SubexpArgumentProgram.writer_eval true a bits (by simpa [a, store, writerStacks] using hp)
  have ha : embedState id writerStacks (state regs w) a = state regs w := by
    apply embedState_eq _ _ Function.injective_id writerStacks_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hb : embedState id writerStacks (state regs w)
      (SubexpArgumentProgram.afterWriter true a bits) =
      state (SubexpArgumentProgram.finishedRegs regs)
        {w with payload := [], record := recordBytes bits ++ w.record} := by
    apply embedState_eq _ _ Function.injective_id writerStacks_injective
    · intro i; rfl
    · intro i; fin_cases i <;> simp [a,
        SubexpArgumentProgram.destination, state, store, writerStacks, recordBytes]
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i hi
      have h4 : i ≠ 4 := fun h => hi ⟨1, h.symm⟩
      have h5 : i ≠ 5 := fun h => hi ⟨3, h.symm⟩
      fin_cases i <;> simp_all [state, store]
  cases hr with
  | call _ ht =>
      have he := eval_call_lifted (SubexpArgumentProgram.writer true) id writerStacks
        (state regs w) Function.injective_id writerStacks_injective ht
      simpa only [writeRecord, ha, hb] using he

theorem one_eval (B : ℕ) (regs : Fin 5 → Bool) (w : Words)
    (hw : w.width.length = B) (hc : w.counter = [])
    (hp : w.payload = []) (hr : w.record = []) (hs : w.scratch = []) :
    ∃ regs', Eval one (22 * B + 24) (state regs w)
      (state regs' {w with
        input := w.input.drop B
        packed := (recordBytes (padTake B w.input)).reverse ++ w.packed}) := by
  let w1 := {w with counter := w.width}
  let w2 := {w1 with
    input := w.input.drop B
    counter := []
    payload := (padTake B w.input).reverse}
  let w3 := {w2 with payload := [], record := recordBytes (padTake B w.input)}
  have h1 := copy_eval (state regs w) 1 2 7 0 1
    (by decide) (by decide) (by decide) (by decide) (by simpa [state, store] using hs)
  have e1 : afterCopy (state regs w) 1 2 0 1 = state (readRegs regs 0 1 none) w1 := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterCopy, StackRoutines.copyStacks, state, store, w1, hc]
  rw [e1] at h1
  obtain ⟨r2, h2⟩ := paddedRead_eval B (readRegs regs 0 1 none) w1 hw
  have h2' : Eval paddedRead (4 * B + 3) (state (readRegs regs 0 1 none) w1)
      (state r2 w2) := by
    simpa only [w2, w1, hp, List.append_nil] using h2
  have h3 := writeRecord_eval r2 w2 (padTake B w.input) rfl
  have h3' : Eval writeRecord (5 * (padTake B w.input).length + 7)
      (state r2 w2) (state (SubexpArgumentProgram.finishedRegs r2) w3) := by
    simpa only [w3, w2, w1, hr, List.append_nil] using h3
  have h4 := transfer_eval (state (SubexpArgumentProgram.finishedRegs r2) w3) 5 6 0 1
    (by decide) (by decide)
  have e4 : afterTransfer (state (SubexpArgumentProgram.finishedRegs r2) w3) 5 6 0 1 =
      state (readRegs (SubexpArgumentProgram.finishedRegs r2) 0 1 none)
        {w with
          input := w.input.drop B
          packed := (recordBytes (padTake B w.input)).reverse ++ w.packed} := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks,
        state, store, w3, w2, w1, hc, hp, hr]
  rw [e4] at h4
  refine ⟨readRegs (SubexpArgumentProgram.finishedRegs r2) 0 1 none, ?_⟩
  have he := h1.seq (h2'.seq (h3'.seq h4))
  convert he using 1
  simp [ state, store, w1, w2, w3, hp, hr, hw, recordBytes,
    Encoding.length_frame, padTake_length, Nat.mul_add, Nat.add_assoc]
  omega

theorem guard_eval (regs : Fin 5 → Bool) (w : Words) :
    Eval guard 1 (state regs w) (state (readRegs regs 0 1 w.todo.head?) w) := by
  exact .base (.atom _ _)

theorem popCount_eval (regs : Fin 5 → Bool) (w : Words) (bit : Bool) (rest : List Bool)
    (hc : w.todo = bit :: rest) :
    Eval popCount 1 (state regs w)
      (state (readRegs regs 0 1 (some bit)) {w with todo := rest}) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (3 : Fin 9) (0 : Fin 5) 1)
    (state regs w)
  apply Eval.base
  convert h using 1
  apply state_ext
  · simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, state, store, hc]
  · funext i; fin_cases i <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, state, store, hc]

theorem finish_eval (regs : Fin 5 → Bool) (w : Words) (ho : w.output = []) :
    Eval finish (3 * w.packed.length + 8) (state regs w)
      (state (readRegs (Function.update regs 0 false) 0 1 none)
        {w with packed := [], output := w.packed.reverse ++ [false]}) := by
  let rr := Function.update regs 0 false
  let w1 := {w with packed := false :: w.packed}
  have h1 : Eval (.base (.atom (.set 0 false))) 1 (state regs w) (state rr w) := by
    exact .base (.atom _ _)
  have h2 : Eval (.base (.atom (.push 6 0))) 1 (state rr w) (state rr w1) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.push (6 : Fin 9) (0 : Fin 5))
      (state rr w)
    apply Eval.base
    convert h using 1
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        state, store, w1, rr]
  have h3 := transfer_eval (state rr w1) 6 8 0 1 (by decide) (by decide)
  have e3 : afterTransfer (state rr w1) 6 8 0 1 =
      state (readRegs rr 0 1 none) {w with packed := [], output := w.packed.reverse ++ [false]} := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> simp [afterTransfer, StackRoutines.transferStacks,
        state, store, w1, ho, List.reverse_cons]
  rw [e3] at h3
  convert h1.seq (h2.seq h3) using 1
  simp [ rr, w1, state, store]
  omega

def chunks (B : ℕ) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | n + 1, input => padTake B input :: chunks B n (input.drop B)

def framedBytes (B n : ℕ) (input : List Bool) : List Bool :=
  (chunks B n input).flatMap recordBytes

@[simp] theorem chunks_length (B n : ℕ) (input : List Bool) : (chunks B n input).length = n := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih => simp [chunks, ih]

theorem framedBytes_length (B n : ℕ) (input : List Bool) :
    (framedBytes B n input).length = n * (2 * B + 2) := by
  induction n generalizing input with
  | zero => simp [framedBytes, chunks]
  | succ n ih =>
      change (recordBytes (padTake B input) ++ framedBytes B n (input.drop B)).length = _
      rw [List.length_append, ih]
      simp only [recordBytes, List.length_cons, Encoding.length_frame, padTake_length,
        Nat.add_mul, Nat.one_mul]
      omega

theorem encode_chunks (B n : ℕ) (input : List Bool) :
    Encoding.encodeList id (chunks B n input) = framedBytes B n input ++ [false] := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih => simp [chunks, framedBytes, recordBytes, Encoding.encodeList, ih, List.append_assoc]

def data (width : List Bool) (n : ℕ) (input packed : List Bool) : Words :=
  {input := input, width := width, todo := List.replicate n true, packed := packed}

theorem loop_eval (width : List Bool) (n : ℕ) (input packed : List Bool) (regs : Fin 5 → Bool) :
    ∃ regs', Eval loop (n * (22 * width.length + 27) + 1)
      (state (readRegs regs 0 1 (List.replicate n true).head?) (data width n input packed))
      (state regs' (data width 0 (input.drop (n * width.length))
        ((framedBytes width.length n input).reverse ++ packed))) := by
  induction n generalizing input packed regs with
  | zero =>
      refine ⟨readRegs regs 0 1 none, ?_⟩
      simpa [loop, data, framedBytes, chunks] using
        (Eval.while_false (body := .seq popCount (.seq one guard))
          (a := state (readRegs regs 0 1 none) (data width 0 input packed))
          (by simp [state, readRegs]))
  | succ n ih =>
      let rs := readRegs regs 0 1 (some true)
      have hp := popCount_eval rs (data width (n + 1) input packed) true
        (List.replicate n true) rfl
      obtain ⟨r1, h1⟩ := one_eval width.length (readRegs rs 0 1 (some true))
        (data width n input packed) rfl rfl rfl rfl rfl
      have hg := guard_eval r1 (data width n (input.drop width.length)
        ((recordBytes (padTake width.length input)).reverse ++ packed))
      obtain ⟨rr, hr⟩ := ih (input.drop width.length)
        ((recordBytes (padTake width.length input)).reverse ++ packed) r1
      have ht : (state rs (data width (n + 1) input packed)).regs 1 = true := by
        simp [state, rs, readRegs]
      have hbody := hp.seq (h1.seq hg)
      have he := Eval.while_true ht hbody hr
      refine ⟨rr, ?_⟩
      convert he using 1 <;>
        simp [ data, rs, framedBytes, chunks, List.drop_drop,
          List.reverse_append, List.append_assoc, Nat.add_mul, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
      all_goals first | rfl | omega

theorem command_eval (width : List Bool) (n : ℕ) (input : List Bool) (regs : Fin 5 → Bool) :
    ∃ regs', Eval command (n * (28 * width.length + 33) + 10)
      (state regs (data width n input []))
      (state regs' {data width 0 (input.drop (n * width.length)) [] with
        output := Encoding.encodeList id (chunks width.length n input)}) := by
  have hg := guard_eval regs (data width n input [])
  obtain ⟨rr, hl⟩ := loop_eval width n input [] regs
  have hf := finish_eval rr (data width 0 (input.drop (n * width.length))
    ((framedBytes width.length n input).reverse ++ [])) rfl
  refine ⟨readRegs (Function.update rr 0 false) 0 1 none, ?_⟩
  have he := hg.seq (hl.seq hf)
  convert he using 1
  · simp [data, framedBytes_length]
    ring
  · simp [data, encode_chunks]

theorem program_trace (width : List Bool) (n : ℕ) (input : List Bool) (regs : Fin 5 → Bool) :
    ∃ regs', Trace program (n * (28 * width.length + 33) + 11)
      ((state regs (data width n input [])).withPC (some program.entry))
      ((state regs' {data width 0 (input.drop (n * width.length)) [] with
        output := Encoding.encodeList id (chunks width.length n input)}).withPC none) := by
  obtain ⟨rr, hr⟩ := command_eval width n input regs
  exact ⟨rr, by simpa [Nat.add_assoc] using compiled_halt_trace hr 0 8⟩

end SubexponentialSAT.SubexpTaylorFrames

end OAI.Algorithms
