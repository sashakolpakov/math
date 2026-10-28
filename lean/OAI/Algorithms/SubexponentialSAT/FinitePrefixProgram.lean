import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.BitProgramBound
import OAI.Algorithms.SubexponentialSAT.SubexpOverhead
import OAI.Algorithms.SubexponentialSAT.FixedParameters
import OAI.Algorithms.SubexponentialSAT.ParserProgram

namespace OAI.Algorithms

/-!
# Actual completion of a solver outside a fixed finite input prefix

The cutoff is fixed in the program. The unary header is inspected by concrete
bit instructions, and every removed input bit is restored before dispatch.
The bounded-variable branch is an actual finite-language scanner compiled to
BitProgram instructions; its finite precomputation uses exhaustive SAT.
-/

namespace SubexponentialSAT.FinitePrefixProgram

open BitProgram
open ParserProgram (pair)

namespace Language

variable {s : ℕ}

@[simp] theorem prod_div {m k : ℕ} (q : Fin m) (i : Fin k) :
    (finProdFinEquiv (q, i)).divNat = q :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (q, i))

@[simp] theorem pair_false : ParserProgram.pair false false = (fun _ : Fin 2 => false) := by
  funext i
  simp [ParserProgram.pair]

@[simp] theorem update_false_pair (b : Bool) :
    Function.update (fun _ : Fin 2 => false) 0 b = ParserProgram.pair b false := by
  simpa only [pair_false] using ParserProgram.update_pair_zero false false b

def addr (scan : FixedParameters.Scanner) (q : Fin scan.states) (stage : Fin 7) :
    Fin (scan.states * 7) := finProdFinEquiv (q, stage)

/-- Three instructions consume each bit. The finite-state transition is a
lookup in the fixed control table, not a runtime operation on an unbounded set. -/
abbrev program (scan : FixedParameters.Scanner) (input output : Fin s) :
    Program 2 s (scan.states * 7) where
  inputStack := input
  outputStack := output
  entry := addr scan scan.start 0
  code label :=
    let q := (finProdFinEquiv.symm label).1
    let stage := (finProdFinEquiv.symm label).2
    match stage.val with
    | 0 => .pop input 0 1 (addr scan q 1)
    | 1 => .branch 1 (addr scan q 2) (addr scan q 3)
    | 2 => .branch 0 (addr scan (scan.next q true) 0) (addr scan (scan.next q false) 0)
    | 3 => .set 0 (scan.accept q) (addr scan q 4)
    | 4 => .push output 0 (addr scan q 5)
    | 5 => .set 0 false (addr scan q 6)
    | _ => .halt

def stores (input : Fin s) (word : List Bool) : Fin s → List Bool :=
  fun i => if i = input then word else []

@[simp] theorem stores_at (input : Fin s) (word : List Bool) : stores input word input = word := by
  simp [stores]

@[simp] theorem stores_nil (input : Fin s) : stores input [] = fun _ => [] := by
  funext i
  simp [stores]

@[simp] theorem update_stores (input : Fin s) (before after : List Bool) :
    Function.update (stores input before) input after = stores input after := by
  funext i
  by_cases hi : i = input <;> simp [stores, hi]

@[simp] theorem update_empty (input : Fin s) (word : List Bool) :
    Function.update (fun _ : Fin s => []) input word = stores input word := by
  rw [← stores_nil input, update_stores]

def cfg (scan : FixedParameters.Scanner) (q : Fin scan.states) (stage : Fin 7)
    (v p : Bool) (stk : Fin s → List Bool) : Cfg 2 s (scan.states * 7) :=
  ⟨some (addr scan q stage), pair v p, stk⟩

theorem consume (scan : FixedParameters.Scanner) (input output : Fin s)
    (q : Fin scan.states) (v p bit : Bool) (word : List Bool) :
    Trace (program scan input output) 3
      (cfg scan q 0 v p (stores input (bit :: word)))
      (cfg scan (scan.next q bit) 0 bit true (stores input word)) := by
  refine .cons (b := cfg scan q 1 bit true (stores input word)) ?_
    (.cons (b := cfg scan q 2 bit true (stores input word)) ?_ (.cons ?_ (.refl _)))
  · simp [step, cfg, addr, execInstr, readRegs]
  · simp [step, cfg, addr, execInstr]
  · cases bit <;> simp [step, cfg, addr, execInstr]

theorem finish (scan : FixedParameters.Scanner) (input output : Fin s)
    (q : Fin scan.states) (v p : Bool) :
    Trace (program scan input output) 6
      (cfg scan q 0 v p (stores input []))
      (terminal (program scan input output) [scan.accept q]) := by
  refine .cons (b := cfg scan q 1 false false (fun _ => [])) ?_
    (.cons (b := cfg scan q 3 false false (fun _ => [])) ?_
      (.cons (b := cfg scan q 4 (scan.accept q) false (fun _ => [])) ?_
        (.cons (b := cfg scan q 5 (scan.accept q) false (stores output [scan.accept q])) ?_
          (.cons (b := cfg scan q 6 false false (stores output [scan.accept q])) ?_
            (.cons ?_ (.refl _))))))
  all_goals simp [step, cfg, addr, execInstr, readRegs, terminal, pair, stores]
  all_goals rfl

/-- A finite-language scanner has an actual linear instruction trace. -/
theorem trace (scan : FixedParameters.Scanner) (input output : Fin s)
    (q : Fin scan.states) (v p : Bool) (word : List Bool) :
    Trace (program scan input output) (3 * word.length + 6)
      (cfg scan q 0 v p (stores input word))
      (terminal (program scan input output)
        [scan.accept (FixedParameters.scannerEval scan q word)]) := by
  induction word generalizing q v p with
  | nil => simpa [FixedParameters.scannerEval] using finish scan input output q v p
  | cons bit word ih =>
      have h := (consume scan input output q v p bit word).trans
        (ih (scan.next q bit) bit true)
      simpa [FixedParameters.scannerEval, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using h

theorem initial_trace (scan : FixedParameters.Scanner) (input output : Fin s)
    (word : List Bool) :
    Trace (program scan input output) (3 * word.length + 6)
      (initial (program scan input output) word)
      (terminal (program scan input output)
        [scan.accept (FixedParameters.scannerEval scan scan.start word)]) := by
  have hi : initial (program scan input output) word =
      cfg scan scan.start 0 false false (stores input word) := by
    simp [initial, cfg ]
    rfl
  rw [hi]
  exact trace scan input output scan.start false false word

noncomputable def smallProgram (N : ℕ) (input output : Fin s) :=
  program (FixedParameters.languageScanner (FixedParameters.smallAcceptedWords N)) input output

theorem small_trace (N n : ℕ) (F : SAT.CNF (Fin n)) (hn : n < N)
    (input output : Fin s) :
    ∃ answer, Trace (smallProgram N input output) (3 * Encoding.formulaBitLength F + 6)
      (initial (smallProgram N input output) (Encoding.encodeCNF F))
      (terminal (smallProgram N input output) [answer]) ∧
      (answer = true ↔ SAT.Satisfiable F) := by
  refine ⟨decide (Encoding.encodeCNF F ∈ FixedParameters.smallAcceptedWords N), ?_, ?_⟩
  · simpa [smallProgram, FixedParameters.languageScanner_accept,
      Encoding.formulaBitLength] using
      initial_trace (FixedParameters.languageScanner (FixedParameters.smallAcceptedWords N))
        input output (Encoding.encodeCNF F)
  · simpa using FixedParameters.smallAcceptedWords_correct N n F (by omega)

end Language

end SubexponentialSAT.FinitePrefixProgram

namespace SubexponentialSAT.FinitePrefixProgram.Header
open StructuredProgram

def triple {α : Type*} (a b c : α) : Fin 3 → α :=
  fun i => if i = 0 then a else if i = 1 then b else c

@[simp] theorem update_zero {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 0 d = triple d b c := by
  funext i
  fin_cases i <;> simp [triple]
@[simp] theorem update_one {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 1 d = triple a d c := by
  funext i
  fin_cases i <;> simp [triple]
@[simp] theorem update_two {α : Type*} (a b c d : α) :
    Function.update (triple a b c) 2 d = triple a b d := by
  funext i
  fin_cases i <;> simp [triple]
@[simp] theorem update_single {α : Type*} (a b : α) :
    Function.update (fun _ : Fin 1 => a) 0 b = fun _ => b := by
  funext i
  fin_cases i
  simp

def state (flag value present : Bool) (input : List Bool) : State 3 1 :=
  ⟨triple flag value present, fun _ => input⟩

theorem set0 (flag value present answer : Bool) (input : List Bool) :
    Eval (.atom (.set 0 answer)) 1 (state flag value present input)
      (state answer value present input) := by
  convert Eval.atom (.set 0 answer) (state flag value present input) using 1
  simp [Atom.eval, Atom.instr, BitProgram.execInstr, State.ofCfg, state]

theorem set1 (flag value present answer : Bool) (input : List Bool) :
    Eval (.atom (.set 1 answer)) 1 (state flag value present input)
      (state flag answer present input) := by
  convert Eval.atom (.set 1 answer) (state flag value present input) using 1
  simp [Atom.eval, Atom.instr, BitProgram.execInstr, State.ofCfg, state]

theorem set2 (flag value present answer : Bool) (input : List Bool) :
    Eval (.atom (.set 2 answer)) 1 (state flag value present input)
      (state flag value answer input) := by
  convert Eval.atom (.set 2 answer) (state flag value present input) using 1
  simp [Atom.eval, Atom.instr, BitProgram.execInstr, State.ofCfg, state]

theorem peek (flag value present bit : Bool) (input : List Bool) :
    Eval (.atom (.peek 0 1 2)) 1 (state flag value present (bit :: input))
      (state flag bit true (bit :: input)) := by
  convert Eval.atom (.peek 0 1 2) (state flag value present (bit :: input)) using 1
  simp [Atom.eval, Atom.instr, BitProgram.execInstr, BitProgram.readRegs, State.ofCfg, state]

theorem pop (flag value present bit : Bool) (input : List Bool) :
    Eval (.atom (.pop 0 1 2)) 1 (state flag value present (bit :: input))
      (state flag bit true input) := by
  convert Eval.atom (.pop 0 1 2) (state flag value present (bit :: input)) using 1
  simp [Atom.eval, Atom.instr, BitProgram.execInstr, BitProgram.readRegs, State.ofCfg, state]

theorem push (flag value present : Bool) (input : List Bool) :
    Eval (.atom (.push 0 1)) 1 (state flag value present input)
      (state flag value present (value :: input)) := by
  convert Eval.atom (.push 0 1) (state flag value present input) using 1
  simp [Atom.eval, Atom.instr, BitProgram.execInstr, State.ofCfg, state, triple]

abbrev reset (answer : Bool) : Cmd 3 1 :=
  .seq (.atom (.set 0 answer)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false)))

theorem reset_eval (flag value present answer : Bool) (input : List Bool) :
    Eval (reset answer) 3 (state flag value present input) (state answer false false input) :=
  .seq (set0 flag value present answer input)
    (.seq (set1 answer value present false input) (set2 answer false present false input))

/-- Fixed-depth header test. Each removed true bit is restored on return from
the statically unrolled subcommand; no auxiliary unbounded counter is used. -/
abbrev trueBody (inner : Cmd 3 1) : Cmd 3 1 :=
  .seq (.atom (.pop 0 1 2))
    (.seq inner (.seq (.atom (.set 1 true))
      (.seq (.atom (.push 0 1)) (.atom (.set 1 false)))))

def command : ℕ → Cmd 3 1
  | 0 => reset true
  | N + 1 => .seq (.atom (.peek 0 1 2))
      (.ite 1 (trueBody (command N)) (reset false))

def time : ℕ → ℕ → ℕ
  | 0, _ => 3
  | _ + 1, 0 => 5
  | N + 1, n + 1 => 6 + time N n

/-- The probe restores the complete raw input and clears its temporary bits. -/
theorem eval (N n : ℕ) (tail : List Bool) (flag value present : Bool) :
    Eval (command N) (time N n)
      (state flag value present (Encoding.encodeNat n ++ tail))
      (state (decide (N ≤ n)) false false (Encoding.encodeNat n ++ tail)) := by
  induction N generalizing n flag value present with
  | zero => simpa [command, time] using reset_eval flag value present true (Encoding.encodeNat n ++ tail)
  | succ N ih =>
      cases n with
      | zero =>
          have h := Eval.seq (peek flag value present false tail)
            (Eval.ite_false (test := (1 : Fin 3)) (yes := trueBody (command N))
              (by simp [state, triple]) (reset_eval flag false true false (false :: tail)))
          simpa [command, time, Encoding.encodeNat] using h
      | succ n =>
          let rest := Encoding.encodeNat n ++ tail
          let answer := decide (N ≤ n)
          have hrestore := Eval.seq (set1 answer false false true rest)
            (Eval.seq (push answer true false rest) (set1 answer true false false (true :: rest)))
          have hbody := Eval.seq (pop flag true true true rest)
            (Eval.seq (ih n flag true true) hrestore)
          have h := Eval.seq (peek flag value present true rest)
            (Eval.ite_true (test := (1 : Fin 3)) (no := reset false) (by simp [state, triple]) hbody)
          convert h using 1 <;>
            simp [command, trueBody, time, Encoding.encodeNat, List.replicate_succ, rest, answer]
          all_goals omega

theorem time_le (N n : ℕ) : time N n ≤ 6 * N + 3 := by
  induction N generalizing n with
  | zero => simp [time]
  | succ N ih =>
      cases n with
      | zero => simp [time]; omega
      | succ n => have h := ih n; simp only [time]; omega

end SubexponentialSAT.FinitePrefixProgram.Header
namespace SubexponentialSAT.FinitePrefixProgram


variable {r s l : ℕ}

def headerRegister (r : ℕ) (i : Fin 3) : Fin (3 + r) := i.castAdd r

def largeRegister (r : ℕ) (i : Fin r) : Fin (3 + r) := i.natAdd 3

def scannerRegister (r : ℕ) (i : Fin 2) : Fin (3 + r) := i.succ.castAdd r

def headerStack (input : Fin s) : Fin 1 → Fin s := fun _ => input

theorem headerRegister_injective (r : ℕ) : Function.Injective (headerRegister r) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simpa [headerRegister] using hh

theorem largeRegister_injective (r : ℕ) : Function.Injective (largeRegister r) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simpa [largeRegister] using hh

theorem scannerRegister_injective (r : ℕ) : Function.Injective (scannerRegister r) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  simpa [scannerRegister] using hh

theorem headerStack_injective (input : Fin s) : Function.Injective (headerStack input) :=
  fun _ _ _ => Subsingleton.elim _ _

/-- Only the first fresh register can be nonzero after header inspection. -/
def ambient (input : Fin s) (flag : Bool) (word : List Bool) : StructuredProgram.State (3 + r) s :=
  ⟨fun i => if i = 0 then flag else false, Language.stores input word⟩

@[simp] theorem ambient_false (input : Fin s) (word : List Bool) :
    ambient (r := r) input false word = StructuredProgram.ioState input word := by
  simp [ambient, StructuredProgram.ioState]
  rfl

/-- The lifted probe touches only its three fresh bits and the input stack. -/
theorem embed_header (input : Fin s) (flag : Bool) (word : List Bool) :
    StructuredCalls.embedState (headerRegister r) (headerStack input) (StructuredProgram.ioState input word)
      (Header.state flag false false word) = ambient (r := r) input flag word := by
  unfold StructuredCalls.embedState StructuredProgram.ioState Header.state ambient
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases hi : ∃ j, headerRegister r j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [(headerRegister_injective r).extend_apply]
      fin_cases j <;> simp [Header.triple, headerRegister, Fin.ext_iff]
    · rw [Function.extend_apply' _ _ _ hi]
      have hne : i ≠ 0 := by
        intro hh
        exact hi ⟨0, by rw [hh]; exact Fin.ext rfl⟩
      simp [hne]
  · funext i
    by_cases hi : i = input
    · subst i
      simpa [headerStack, Language.stores] using
        (headerStack_injective input).extend_apply (fun _ => word)
          (fun i => if i = input then word else []) 0
    · have hn : ¬ ∃ j, headerStack input j = i := by
        simpa [headerStack, eq_comm] using hi
      rw [Function.extend_apply' _ _ _ hn]
      rfl

def headerRoutine (N : ℕ) := StructuredProgram.compiled (Header.command N) 0 0

abbrev liftedHeader (p : BitProgram.Program r s l) (N : ℕ) :=
  ProgramLinking.liftProgram (headerRoutine N) (headerRegister r) (headerStack p.inputStack)

abbrev liftedLarge (p : BitProgram.Program r s l) :=
  ProgramLinking.liftProgram p (largeRegister r) id

noncomputable def liftedSmall (p : BitProgram.Program r s l) (N : ℕ) :=
  ProgramLinking.liftProgram (Language.smallProgram N p.inputStack p.outputStack) (scannerRegister r) id

theorem header_call (p : BitProgram.Program r s l) (N n : ℕ) (tail : List Bool) :
    StructuredCalls.Eval (.call (liftedHeader p N)) (Header.time N n + 1)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeNat n ++ tail))
      (ambient (r := r) p.inputStack (decide (N ≤ n)) (Encoding.encodeNat n ++ tail)) := by
  have ht := StructuredProgram.compiled_halt_trace (Header.eval N n tail false false false) 0 0
  have hc := StructuredCalls.eval_call_lifted (headerRoutine N) (headerRegister r) (headerStack p.inputStack)
    (StructuredProgram.ioState p.inputStack (Encoding.encodeNat n ++ tail))
    (headerRegister_injective r) (headerStack_injective p.inputStack) ht
  simpa only [embed_header, ambient_false] using hc

/-- Lift any canonical actual source trace into a larger register bank. -/
theorem call_io {R : ℕ} (p : BitProgram.Program r s l) (register : Fin r → Fin R)
    (hregister : Function.Injective register) {n : ℕ} {input output : List Bool}
    (h : BitProgram.Trace p n (BitProgram.initial p input) (BitProgram.terminal p output)) :
    StructuredCalls.Eval (.call (ProgramLinking.liftProgram p register id)) n
      (StructuredProgram.ioState p.inputStack input) (StructuredProgram.ioState p.outputStack output) := by
  have ht : BitProgram.Trace p n
      ((StructuredProgram.ioState p.inputStack input).withPC (some p.entry))
      ((StructuredProgram.ioState p.outputStack output).withPC none) := h
  have hc := StructuredCalls.eval_call_lifted p register id (StructuredProgram.ioState p.inputStack input)
    hregister Function.injective_id ht
  simpa [StructuredCalls.embedState, StructuredProgram.ioState, ProgramLinking.extend_id] using hc

@[simp] theorem reset_flag (flag : Bool) :
    Function.update (fun i : Fin (3 + r) => if i = 0 then flag else false) 0 false =
      (fun _ => false) := by
  funext i
  by_cases hi : i = 0 <;> simp [hi]

theorem clear_flag (input : Fin s) (word : List Bool) :
    StructuredCalls.Eval (.base (.atom (.set (0 : Fin (3 + r)) false))) 1
      (ambient input true word) (StructuredProgram.ioState input word) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.set (0 : Fin (3 + r)) false) (ambient input true word) using 1
  simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    BitProgram.execInstr, ambient, StructuredProgram.ioState]
  simp only [reset_flag]
  rfl

/-- The large routine is entered with exactly its original input and cleared
work bits. All extra control bits are cleared before the call. -/
noncomputable abbrev command (p : BitProgram.Program r s l) (N : ℕ) : StructuredCalls.Cmd (3 + r) s :=
  .seq (.call (liftedHeader p N))
    (.ite 0
      (.seq (.base (.atom (.set 0 false))) (.call (liftedLarge p)))
      (.call (liftedSmall p N)))

noncomputable def completed (p : BitProgram.Program r s l) (N : ℕ) :=
  StructuredCalls.compiled (command p N) p.inputStack p.outputStack

end SubexponentialSAT.FinitePrefixProgram
namespace SubexponentialSAT.FinitePrefixProgram

variable {r s l : ℕ}

/-- Exact composed source execution on the large branch. -/
theorem large_eval (p : BitProgram.Program r s l) (N n : ℕ) (F : SAT.CNF (Fin n))
    (hn : N ≤ n) {steps : ℕ} {answer : Bool}
    (hrun : BitProgram.Trace p steps (BitProgram.initial p (Encoding.encodeCNF F))
      (BitProgram.terminal p [answer])) :
    StructuredCalls.Eval (command p N) (Header.time N n + steps + 3)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F))
      (StructuredProgram.ioState p.outputStack [answer]) := by
  have hh : StructuredCalls.Eval (.call (liftedHeader p N)) (Header.time N n + 1)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F))
      (ambient (r := r) p.inputStack true (Encoding.encodeCNF F)) := by
    simpa [hn, Encoding.encodeCNF] using header_call p N n (Encoding.encodeCNFBody F)
  have hl : StructuredCalls.Eval (.call (liftedLarge p)) steps
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F))
      (StructuredProgram.ioState p.outputStack [answer]) :=
    call_io p (largeRegister r) (largeRegister_injective r) hrun
  have hb := StructuredCalls.Eval.seq (clear_flag p.inputStack (Encoding.encodeCNF F)) hl
  have hg := StructuredCalls.Eval.ite_true (test := (0 : Fin (3 + r)))
    (no := .call (liftedSmall p N)) (by simp [ambient]) hb
  have h := StructuredCalls.Eval.seq hh hg
  convert h using 1; omega

/-- Exact composed source execution and SAT correctness on the bounded branch. -/
theorem small_eval (p : BitProgram.Program r s l) (N n : ℕ) (F : SAT.CNF (Fin n))
    (hn : n < N) :
    ∃ answer, StructuredCalls.Eval (command p N)
      (Header.time N n + 3 * Encoding.formulaBitLength F + 8)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F))
      (StructuredProgram.ioState p.outputStack [answer]) ∧
      (answer = true ↔ SAT.Satisfiable F) := by
  obtain ⟨answer, hsmall, hsat⟩ := Language.small_trace N n F hn p.inputStack p.outputStack
  have hh : StructuredCalls.Eval (.call (liftedHeader p N)) (Header.time N n + 1)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F))
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F)) := by
    simpa [show ¬ N ≤ n by omega, Encoding.encodeCNF] using
      header_call p N n (Encoding.encodeCNFBody F)
  have hs : StructuredCalls.Eval (.call (liftedSmall p N))
      (3 * Encoding.formulaBitLength F + 6)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F))
      (StructuredProgram.ioState p.outputStack [answer]) :=
    call_io (Language.smallProgram N p.inputStack p.outputStack)
      (scannerRegister r) (scannerRegister_injective r) hsmall
  have hg := StructuredCalls.Eval.ite_false (test := (0 : Fin (3 + r)))
    (yes := .seq (.base (.atom (.set 0 false))) (.call (liftedLarge p)))
    (by rfl) hs
  have h := StructuredCalls.Eval.seq hh hg
  refine ⟨answer, ?_, hsat⟩
  convert h using 1; omega

/-- The actual completed finite program uses only fixed additive overhead on
the large branch, in addition to the original measured source execution. -/
theorem completed_large (p : BitProgram.Program r s l) (N n : ℕ) (F : SAT.CNF (Fin n))
    (hn : N ≤ n) {bound : ℕ} {answer : Bool}
    (hrun : BitProgram.RunsIn p bound (BitProgram.initial p (Encoding.encodeCNF F))
      (BitProgram.terminal p [answer])) :
    BitProgram.RunsIn (completed p N) (6 * N + bound + 7)
      (BitProgram.initial (completed p N) (Encoding.encodeCNF F))
      (BitProgram.terminal (completed p N) [answer]) := by
  obtain ⟨steps, hsteps, ht⟩ := hrun
  have h := StructuredCalls.compiled_io_trace p.inputStack p.outputStack (large_eval p N n F hn ht)
  refine ⟨_, ?_, h⟩
  have hb := Header.time_le N n
  omega

/-- The bounded branch consumes the whole input with an actual finite scanner. -/
theorem completed_small (p : BitProgram.Program r s l) (N n : ℕ) (F : SAT.CNF (Fin n))
    (hn : n < N) :
    ∃ answer, BitProgram.RunsIn (completed p N)
      (6 * N + 3 * Encoding.formulaBitLength F + 12)
      (BitProgram.initial (completed p N) (Encoding.encodeCNF F))
      (BitProgram.terminal (completed p N) [answer]) ∧
      (answer = true ↔ SAT.Satisfiable F) := by
  obtain ⟨answer, he, hsat⟩ := small_eval p N n F hn
  refine ⟨answer, ⟨_, ?_, StructuredCalls.compiled_io_trace p.inputStack p.outputStack he⟩, hsat⟩
  have hb := Header.time_le N n
  omega

/-- Complete a fixed eventual solver without changing it as the input varies.
The only algorithmic hypothesis is the original large program's actual run. -/
theorem completes_eventual (p : BitProgram.Program r s l) (N width : ℕ)
    (time : ℕ → ℕ → ℕ)
    (large : ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F → N ≤ n →
      ∃ answer, BitProgram.RunsIn p (time n (Encoding.formulaBitLength F))
        (BitProgram.initial p (Encoding.encodeCNF F)) (BitProgram.terminal p [answer]) ∧
        (answer = true ↔ SAT.Satisfiable F)) :
    ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
      ∃ answer, BitProgram.RunsIn (completed p N)
        (6 * N + 3 * Encoding.formulaBitLength F + time n (Encoding.formulaBitLength F) + 12)
        (BitProgram.initial (completed p N) (Encoding.encodeCNF F))
        (BitProgram.terminal (completed p N) [answer]) ∧
        (answer = true ↔ SAT.Satisfiable F) := by
  intro n F hwidth
  by_cases hn : N ≤ n
  · obtain ⟨answer, hrun, hsat⟩ := large n F hwidth hn
    exact ⟨answer, (completed_large p N n F hn hrun).mono (by omega), hsat⟩
  · obtain ⟨answer, hrun, hsat⟩ := completed_small p N n F (by omega)
    exact ⟨answer, hrun.mono (by omega), hsat⟩

/-- Strict primitive-machine completion, with a single program-fixed
multiplicative simulation constant and the proved additive input-scan cost. -/
theorem primitive_completes_eventual (p : BitProgram.Program r s l) (N width : ℕ)
    (time : ℕ → ℕ → ℕ)
    (large : ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F → N ≤ n →
      ∃ answer, BitProgram.RunsIn p (time n (Encoding.formulaBitLength F))
        (BitProgram.initial p (Encoding.encodeCNF F)) (BitProgram.terminal p [answer]) ∧
        (answer = true ↔ SAT.Satisfiable F)) :
    ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
      ∃ answer, (BitProgram.primitive (completed p N)).OutputsInTime
        (Encoding.encodeCNF F) answer
        (BitProgram.primitiveOverhead (completed p N) *
          (6 * N + 3 * Encoding.formulaBitLength F + time n (Encoding.formulaBitLength F) + 12)) ∧
        (answer = true ↔ SAT.Satisfiable F) := by
  intro n F hwidth
  obtain ⟨answer, hrun, hsat⟩ := completes_eventual p N width time large n F hwidth
  exact ⟨answer, BitProgram.primitive_outputs _ hrun, hsat⟩

end SubexponentialSAT.FinitePrefixProgram

namespace SubexponentialSAT.FinitePrefixProgram

variable {r s l : ℕ}

/-- Final work data of the large routine embedded into the completed program.
The three fresh control bits are zero; all source work data is retained. -/
noncomputable def largeData (final : BitProgram.Cfg r s l) : StructuredProgram.State (3 + r) s :=
  ⟨Function.extend (largeRegister r) final.regs (fun _ => false), final.stacks⟩

theorem large_call_dirty (p : BitProgram.Program r s l) {steps : ℕ}
    {input : List Bool} {final : BitProgram.Cfg r s l}
    (hrun : BitProgram.Trace p steps (BitProgram.initial p input) final)
    (halted : final.pc = none) :
    StructuredCalls.Eval (.call (liftedLarge p)) steps
      (StructuredProgram.ioState p.inputStack input) (largeData final) := by
  have hf : (StructuredProgram.State.ofCfg final).withPC none = final := by
    rcases final with ⟨pc, regs, stk⟩
    change pc = none at halted
    subst pc
    rfl
  have ht : BitProgram.Trace p steps
      ((StructuredProgram.ioState p.inputStack input).withPC (some p.entry))
      ((StructuredProgram.State.ofCfg final).withPC none) := by
    rw [hf]
    simpa only [BitProgram.initial, StructuredProgram.ioState,
      StructuredProgram.State.withPC] using hrun
  have hc := StructuredCalls.eval_call_lifted p (largeRegister r) id
    (StructuredProgram.ioState p.inputStack input)
    (largeRegister_injective r) Function.injective_id ht
  simpa [StructuredCalls.embedState, StructuredProgram.ioState,
    StructuredProgram.State.ofCfg, ProgramLinking.extend_id, largeData] using hc

/-- The large branch permits arbitrary halted source work storage. -/
theorem large_eval_dirty (p : BitProgram.Program r s l) (N n : ℕ) (F : SAT.CNF (Fin n))
    (hn : N ≤ n) {steps : ℕ} {final : BitProgram.Cfg r s l}
    (hrun : BitProgram.Trace p steps (BitProgram.initial p (Encoding.encodeCNF F)) final)
    (halted : final.pc = none) :
    StructuredCalls.Eval (command p N) (Header.time N n + steps + 3)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F)) (largeData final) := by
  have hh : StructuredCalls.Eval (.call (liftedHeader p N)) (Header.time N n + 1)
      (StructuredProgram.ioState p.inputStack (Encoding.encodeCNF F))
      (ambient (r := r) p.inputStack true (Encoding.encodeCNF F)) := by
    simpa [hn, Encoding.encodeCNF] using header_call p N n (Encoding.encodeCNFBody F)
  have hb := StructuredCalls.Eval.seq (clear_flag p.inputStack (Encoding.encodeCNF F))
    (large_call_dirty p hrun halted)
  have hg := StructuredCalls.Eval.ite_true (test := (0 : Fin (3 + r)))
    (no := .call (liftedSmall p N)) (by simp [ambient]) hb
  have h := StructuredCalls.Eval.seq hh hg
  convert h using 1; omega

/-- No cleanup of source work storage is necessary for finite-prefix completion. -/
theorem completed_large_dirty (p : BitProgram.Program r s l) (N n : ℕ) (F : SAT.CNF (Fin n))
    (hn : N ≤ n) {bound : ℕ} {final : BitProgram.Cfg r s l}
    (hrun : BitProgram.RunsIn p bound (BitProgram.initial p (Encoding.encodeCNF F)) final)
    (halted : final.pc = none) :
    BitProgram.RunsIn (completed p N) (6 * N + bound + 7)
      (BitProgram.initial (completed p N) (Encoding.encodeCNF F))
      ((largeData final).withPC none) := by
  obtain ⟨steps, hsteps, ht⟩ := hrun
  have h := StructuredCalls.compiled_halt_trace (large_eval_dirty p N n F hn ht halted)
    p.inputStack p.outputStack
  refine ⟨_, ?_, h⟩
  have hb := Header.time_le N n
  omega

/-- General source contract: arbitrary halted work data, with the answer at the
head of the designated output stack. -/
theorem completes_eventual_dirty (p : BitProgram.Program r s l) (N width : ℕ)
    (time : ℕ → ℕ → ℕ)
    (large : ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F → N ≤ n →
      ∃ (final : BitProgram.Cfg r s l) (answer : Bool),
        BitProgram.RunsIn p (time n (Encoding.formulaBitLength F))
          (BitProgram.initial p (Encoding.encodeCNF F)) final ∧
        final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
        (answer = true ↔ SAT.Satisfiable F)) :
    ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
      ∃ final answer, BitProgram.RunsIn (completed p N)
        (6 * N + 3 * Encoding.formulaBitLength F + time n (Encoding.formulaBitLength F) + 12)
        (BitProgram.initial (completed p N) (Encoding.encodeCNF F)) final ∧
        final.pc = none ∧ (final.stacks (completed p N).outputStack).head? = some answer ∧
        (answer = true ↔ SAT.Satisfiable F) := by
  intro n F hwidth
  by_cases hn : N ≤ n
  · obtain ⟨final, answer, hrun, hhalted, hout, hsat⟩ := large n F hwidth hn
    refine ⟨(largeData final).withPC none, answer,
      (completed_large_dirty p N n F hn hrun hhalted).mono (by omega), rfl, ?_, hsat⟩
    exact hout
  · obtain ⟨answer, hrun, hsat⟩ := completed_small p N n F (by omega)
    refine ⟨BitProgram.terminal (completed p N) [answer], answer,
      hrun.mono (by omega), rfl, ?_, hsat⟩
    simp []

/-- The complete primitive solver retains the large routine's dirty halted
state convention and uses only a fixed multiplicative compiler overhead. -/
theorem primitive_completes_eventual_dirty (p : BitProgram.Program r s l) (N width : ℕ)
    (time : ℕ → ℕ → ℕ)
    (large : ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F → N ≤ n →
      ∃ (final : BitProgram.Cfg r s l) (answer : Bool),
        BitProgram.RunsIn p (time n (Encoding.formulaBitLength F))
          (BitProgram.initial p (Encoding.encodeCNF F)) final ∧
        final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
        (answer = true ↔ SAT.Satisfiable F)) :
    ∀ n (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
      ∃ answer, (BitProgram.primitive (completed p N)).OutputsInTime
        (Encoding.encodeCNF F) answer
        (BitProgram.primitiveOverhead (completed p N) *
          (6 * N + 3 * Encoding.formulaBitLength F + time n (Encoding.formulaBitLength F) + 12)) ∧
        (answer = true ↔ SAT.Satisfiable F) := by
  intro n F hwidth
  obtain ⟨final, answer, hrun, hhalted, hout, hsat⟩ :=
    completes_eventual_dirty p N width time large n F hwidth
  exact ⟨answer, BitProgram.primitive_outputs_of_halted _ hrun hhalted hout, hsat⟩

end SubexponentialSAT.FinitePrefixProgram
namespace SubexponentialSAT.FinitePrefixProgram

variable {r s l : ℕ}

/-- An eventual source-program bound still refers to actual measured runs and
an explicit output bit. It permits arbitrary remaining work data. -/
def DecidesAbove (p : BitProgram.Program r s l) (N width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F → N ≤ n →
    ∃ (answer : Bool) (time : ℕ) (final : BitProgram.Cfg r s l),
      BitProgram.RunsIn p time (BitProgram.initial p (Encoding.encodeCNF F)) final ∧
      final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
        (Encoding.formulaBitLength F) n

/-- Fixed cutoff and linear input-scan costs fit the same exponent and degree. -/
theorem completion_overhead_le {constant exponentConstant : ℝ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant) {degree : ℕ} (hd : 0 < degree)
    (N L n sourceTime : ℕ)
    (hsource : (sourceTime : ℝ) ≤
      SubexpComputation.runtimeBound constant exponentConstant degree L n) :
    ((6 * N + 3 * L + sourceTime + 12 : ℕ) : ℝ) ≤
      SubexpComputation.runtimeBound (((6 * N + 16 : ℕ) : ℝ) * (2 * constant))
        exponentConstant degree L n := by
  have hnat : 6 * N + 3 * L + sourceTime + 12 ≤
      (6 * N + 16) * (sourceTime + L + 1) ^ 1 := by
    simp only [pow_one]
    nlinarith
  simpa using SubexpComputation.nat_polynomial_overhead_le hc ha hd
    L n 1 (6 * N + 16) sourceTime (6 * N + 3 * L + sourceTime + 12) hsource hnat

/-- Complete the actual large-input source program and its real-valued
subexponential bound. No cleanup or additional compiler hypothesis is needed. -/
theorem completed_decidesWithBound (p : BitProgram.Program r s l) (N width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant) (hd : 0 < degree)
    (large : DecidesAbove p N width constant exponentConstant degree) :
    BitProgram.DecidesWithBound (completed p N) width
      (((6 * N + 16 : ℕ) : ℝ) * (2 * constant)) exponentConstant degree := by
  intro n F hwidth
  by_cases hn : N ≤ n
  · obtain ⟨answer, time, final, hrun, hhalted, hout, hsat, hbound⟩ := large n F hwidth hn
    refine ⟨answer, 6 * N + 3 * Encoding.formulaBitLength F + time + 12,
      (largeData final).withPC none,
      (completed_large_dirty p N n F hn hrun hhalted).mono (by omega), rfl, hout, hsat, ?_⟩
    exact completion_overhead_le hc ha hd N _ n time hbound
  · obtain ⟨answer, hrun, hsat⟩ := completed_small p N n F (by omega)
    refine ⟨answer, 6 * N + 3 * Encoding.formulaBitLength F + 12,
      BitProgram.terminal (completed p N) [answer], hrun, rfl, ?_, hsat, ?_⟩
    · simp []
    · have hz : (0 : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
          (Encoding.formulaBitLength F) n :=
        SubexpComputation.runtimeBound_nonneg (by linarith) _ _ _ _
      simpa using completion_overhead_le hc ha hd N (Encoding.formulaBitLength F) n 0
        (by simpa only [Nat.cast_zero] using hz)

/-- A fixed eventual source solver with positive exponent and polynomial
degree therefore yields the full strict primitive-machine feasibility target. -/
theorem feasible_of_eventual_program (p : BitProgram.Program r s l) (N width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 < exponentConstant) (hd : 0 < degree)
    (large : DecidesAbove p N width constant exponentConstant degree) :
    SubexpComputation.Feasible width := by
  apply BitProgram.feasible_of_program (completed p N) (degree := degree)
    (constant := ((6 * N + 16 : ℕ) : ℝ) * (2 * constant))
    (exponentConstant := exponentConstant)
  · have hconstant : 0 < constant := lt_of_lt_of_le (by norm_num) hc
    positivity
  · exact ha
  · exact hd
  · exact completed_decidesWithBound p N width hc ha.le hd large

/-- A cutoff chosen from an eventual assertion is still chosen before the
varying input. The same completed machine then handles every formula size. -/
theorem feasible_of_eventually_bounded_program (p : BitProgram.Program r s l) (width : ℕ)
    {constant exponentConstant : ℝ} {degree : ℕ}
    (hc : 1 ≤ constant) (ha : 0 < exponentConstant) (hd : 0 < degree)
    (large : ∀ᶠ n in Filter.atTop,
      ∀ (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
        ∃ (answer : Bool) (time : ℕ) (final : BitProgram.Cfg r s l),
          BitProgram.RunsIn p time (BitProgram.initial p (Encoding.encodeCNF F)) final ∧
          final.pc = none ∧ (final.stacks p.outputStack).head? = some answer ∧
          (answer = true ↔ SAT.Satisfiable F) ∧
          (time : ℝ) ≤ SubexpComputation.runtimeBound constant exponentConstant degree
            (Encoding.formulaBitLength F) n) :
    SubexpComputation.Feasible width := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp large
  exact feasible_of_eventual_program p N width hc ha hd
    (fun n F hwidth hn => hN n hn F hwidth)

end SubexponentialSAT.FinitePrefixProgram

end OAI.Algorithms
