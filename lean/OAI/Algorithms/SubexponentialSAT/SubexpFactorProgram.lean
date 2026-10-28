import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ParserProgram
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.ArrayPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.FactorReduction

namespace OAI.Algorithms

/-!
# Concrete factor-row evaluation primitives

Programs in this module have fixed Boolean registers and fixed finite control.
Inputs are working copies on stacks. All costs below are actual instruction
traces; neither arithmetic comparisons nor semantic predicates are instructions.
-/

namespace SubexponentialSAT.SubexpFactorProgram

open SubexponentialSAT.BitProgram

def allZero : List Bool → Bool
  | [] => true
  | b :: bs => !b && allZero bs

theorem allZero_iff_toNat_zero (bs : List Bool) :
    allZero bs = true ↔ BinaryArithmetic.toNat bs = 0 := by
  induction bs with
  | nil => simp [allZero]
  | cons b bs ih => cases b <;> simp [allZero, BinaryArithmetic.toNat, ih]

theorem toNat_append (low high : List Bool) :
    BinaryArithmetic.toNat (low ++ high) =
      BinaryArithmetic.toNat low + 2 ^ low.length * BinaryArithmetic.toNat high := by
  induction low with
  | nil => simp
  | cons b low ih => simp only [List.cons_append, BinaryArithmetic.toNat_cons,
      List.length_cons, ih, pow_succ]; ring

theorem toNat_lt_pow_length (bs : List Bool) :
    BinaryArithmetic.toNat bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b <;> simp only [BinaryArithmetic.toNat_cons, BinaryArithmetic.bitVal_false,
      BinaryArithmetic.bitVal_true, List.length_cons, pow_succ] <;> omega

/-- A padded little-endian label is below `2^b` exactly when all bits beyond
its `b` low bits are zero. No comparison is being assigned unit cost. -/
theorem unary_validity_iff (low high : List Bool) :
    allZero high = true ↔ BinaryArithmetic.toNat (low ++ high) < 2 ^ low.length := by
  rw [allZero_iff_toNat_zero, toNat_append]
  have hl := toNat_lt_pow_length low
  have hp : 0 < 2 ^ low.length := pow_pos (by decide) _
  constructor
  · intro h; simp [h, hl]
  · intro h
    by_contra hz
    have hge : 1 ≤ BinaryArithmetic.toNat high := by omega
    have hm := Nat.mul_le_mul_left (2 ^ low.length) hge
    omega

namespace ZeroBits

def regs (acc bit present : Bool) : Fin 3 → Bool :=
  fun i => if i = 0 then acc else if i = 1 then bit else present

@[simp] theorem regs_zero (a b p : Bool) : regs a b p 0 = a := rfl
@[simp] theorem regs_one (a b p : Bool) : regs a b p 1 = b := rfl
@[simp] theorem regs_two (a b p : Bool) : regs a b p 2 = p := rfl

@[simp] theorem update_zero (a b p c : Bool) : Function.update (regs a b p) 0 c = regs c b p := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem update_one (a b p c : Bool) : Function.update (regs a b p) 1 c = regs a c p := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem update_two (a b p c : Bool) : Function.update (regs a b p) 2 c = regs a b c := by
  funext i; fin_cases i <;> simp [regs]

abbrev cfg (pc : Option (Fin 10)) (a b p : Bool) (input output : List Bool) : Cfg 3 2 10 :=
  ⟨pc, regs a b p, ParserProgram.pair input output⟩

/-- Consume a bit word and output whether every bit is zero. -/
abbrev program : Program 3 2 10 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 true 1
    | 1 => .pop 0 1 2 2
    | 2 => .branch 2 3 5
    | 3 => .bnot 1 1 4
    | 4 => .band 0 0 1 1
    | 5 => .push 1 0 6
    | 6 => .set 0 false 7
    | 7 => .set 1 false 8
    | 8 => .set 2 false 9
    | _ => .halt

theorem cycle (a b p x : Bool) (xs out : List Bool) :
    Trace program 4 (cfg (some 1) a b p (x :: xs) out)
      (cfg (some 1) (a && !x) (!x) true xs out) := by
  refine .cons (b := cfg (some 2) a x true xs out) ?_
    (.cons (b := cfg (some 3) a x true xs out) ?_
      (.cons (b := cfg (some 4) a (!x) true xs out) ?_
        (.cons ?_ (.refl _))))
  all_goals simp [step, cfg, execInstr, readRegs]

theorem finish (a b p : Bool) (out : List Bool) :
    Trace program 7 (cfg (some 1) a b p [] out)
      (cfg none false false false [] (a :: out)) := by
  refine .cons (b := cfg (some 2) a false false [] out) ?_
    (.cons (b := cfg (some 5) a false false [] out) ?_
      (.cons (b := cfg (some 6) a false false [] (a :: out)) ?_
        (.cons (b := cfg (some 7) false false false [] (a :: out)) ?_
          (.cons (b := cfg (some 8) false false false [] (a :: out)) ?_
            (.cons (b := cfg (some 9) false false false [] (a :: out)) ?_
              (.cons ?_ (.refl _)))))))
  all_goals simp [step, cfg, execInstr, readRegs]

theorem loop_trace (xs out : List Bool) (a b p : Bool) :
    Trace program (4 * xs.length + 7) (cfg (some 1) a b p xs out)
      (cfg none false false false [] ((a && allZero xs) :: out)) := by
  induction xs generalizing a b p with
  | nil => simpa [allZero] using finish a b p out
  | cons x xs ih =>
    have h := (cycle a b p x xs out).trans (ih (a && !x) (!x) true)
    convert h using 1 <;> simp [allZero, List.length_cons, Bool.and_assoc] ; omega

theorem trace (xs : List Bool) :
    Trace program (4 * xs.length + 8) (initial program xs)
      (terminal program [allZero xs]) := by
  have hstart : step program (cfg (some 0) false false false xs []) =
      some (cfg (some 1) true false false xs []) := by
    simp [step, cfg, execInstr]
  have h := Computation.Trace.cons hstart (loop_trace xs [] true false false)
  have hr : regs false false false = fun _ => false := by funext i; simp [regs]
  have hi : cfg (some 0) false false false xs [] = initial program xs := by
    simp [initial, cfg, hr ]
    rfl
  have ht : cfg none false false false [] [allZero xs] = terminal program [allZero xs] := by
    simp only [cfg, terminal, hr]
    congr 1
    funext i
    fin_cases i <;> rfl
  simpa only [Bool.true_and, hi, ht, Nat.add_assoc] using h

/-- The fixed program runs on the primitive machine with its proved overhead. -/
theorem primitive_outputs (xs : List Bool) :
    (BitProgram.primitive program).OutputsInTime xs (allZero xs)
      (BitProgram.primitiveOverhead program * (4 * xs.length + 8)) :=
  BitProgram.primitive_outputs program ⟨_, le_rfl, trace xs⟩

end ZeroBits

namespace SignedClause

def truth (sign value : Bool) : Bool := !(sign ^^ value)

def encodePairs : List (Bool × Bool) → List Bool
  | [] => []
  | (sign, value) :: xs => sign :: value :: encodePairs xs

def evalPairs : List (Bool × Bool) → Bool
  | [] => false
  | (sign, value) :: xs => truth sign value || evalPairs xs

theorem truth_eq_eval {V : Type*} (a : SAT.Assignment V) (l : SAT.Literal V) :
    truth l.positive (a l.variable) = l.eval a := by
  cases h : l.positive <;> cases hv : a l.variable <;> simp [truth, SAT.Literal.eval, h, hv]

theorem evalPairs_map {V : Type*} (a : SAT.Assignment V) (ls : List (SAT.Literal V)) :
    evalPairs (ls.map fun l => (l.positive, a l.variable)) = ls.any (fun l => l.eval a) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.map_cons, evalPairs, truth_eq_eval, ih, List.any_cons]

/-- A row stream contains the actual sign and looked-up variable bit for each
literal. Producing the looked-up bits is a separate caller operation. -/
theorem evalPairs_clause {V : Type*} [DecidableEq V]
    (a : SAT.Assignment V) (ls : List (SAT.Literal V)) (C : SAT.Clause V)
    (hls : ls.toFinset = C) :
    evalPairs (ls.map fun l => (l.positive, a l.variable)) = C.eval a := by
  rw [evalPairs_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, SAT.Clause.eval_eq_true]
  simp only [← hls, List.mem_toFinset]

def regs (acc sign value present temp : Bool) : Fin 5 → Bool :=
  fun i => if i = 0 then acc else if i = 1 then sign else if i = 2 then value
    else if i = 3 then present else temp

@[simp] theorem regs_zero (a s v p t : Bool) : regs a s v p t 0 = a := rfl
@[simp] theorem regs_one (a s v p t : Bool) : regs a s v p t 1 = s := rfl
@[simp] theorem regs_two (a s v p t : Bool) : regs a s v p t 2 = v := rfl
@[simp] theorem regs_three (a s v p t : Bool) : regs a s v p t 3 = p := rfl
@[simp] theorem regs_four (a s v p t : Bool) : regs a s v p t 4 = t := rfl

@[simp] theorem update_zero (a s v p t c : Bool) :
    Function.update (regs a s v p t) 0 c = regs c s v p t := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem update_one (a s v p t c : Bool) :
    Function.update (regs a s v p t) 1 c = regs a c v p t := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem update_two (a s v p t c : Bool) :
    Function.update (regs a s v p t) 2 c = regs a s c p t := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem update_three (a s v p t c : Bool) :
    Function.update (regs a s v p t) 3 c = regs a s v c t := by
  funext i; fin_cases i <;> simp [regs]
@[simp] theorem update_four (a s v p t c : Bool) :
    Function.update (regs a s v p t) 4 c = regs a s v p c := by
  funext i; fin_cases i <;> simp [regs]

abbrev cfg (pc : Option (Fin 14)) (a s v p t : Bool) (input output : List Bool) : Cfg 5 2 14 :=
  ⟨pc, regs a s v p t, ParserProgram.pair input output⟩

/-- A fixed-control evaluator for interleaved sign/value row data. -/
abbrev program : Program 5 2 14 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .set 0 false 1
    | 1 => .pop 0 1 3 2
    | 2 => .branch 3 3 7
    | 3 => .pop 0 2 3 4
    | 4 => .bxor 4 1 2 5
    | 5 => .bnot 4 4 6
    | 6 => .bor 0 0 4 1
    | 7 => .push 1 0 8
    | 8 => .set 0 false 9
    | 9 => .set 1 false 10
    | 10 => .set 2 false 11
    | 11 => .set 3 false 12
    | 12 => .set 4 false 13
    | _ => .halt

theorem cycle (a s v p t sign value : Bool) (xs out : List Bool) :
    Trace program 6 (cfg (some 1) a s v p t (sign :: value :: xs) out)
      (cfg (some 1) (a || truth sign value) sign value true (truth sign value) xs out) := by
  refine .cons (b := cfg (some 2) a sign v true t (value :: xs) out) ?_
    (.cons (b := cfg (some 3) a sign v true t (value :: xs) out) ?_
      (.cons (b := cfg (some 4) a sign value true t xs out) ?_
        (.cons (b := cfg (some 5) a sign value true (sign ^^ value) xs out) ?_
          (.cons (b := cfg (some 6) a sign value true (truth sign value) xs out) ?_
            (.cons ?_ (.refl _))))))
  all_goals simp [step, cfg, execInstr, readRegs, truth]

theorem finish (a s v p t : Bool) (out : List Bool) :
    Trace program 9 (cfg (some 1) a s v p t [] out)
      (cfg none false false false false false [] (a :: out)) := by
  refine .cons (b := cfg (some 2) a false v false t [] out) ?_
    (.cons (b := cfg (some 7) a false v false t [] out) ?_
      (.cons (b := cfg (some 8) a false v false t [] (a :: out)) ?_
        (.cons (b := cfg (some 9) false false v false t [] (a :: out)) ?_
          (.cons (b := cfg (some 10) false false v false t [] (a :: out)) ?_
            (.cons (b := cfg (some 11) false false false false t [] (a :: out)) ?_
              (.cons (b := cfg (some 12) false false false false t [] (a :: out)) ?_
                (.cons (b := cfg (some 13) false false false false false [] (a :: out)) ?_
                  (.cons ?_ (.refl _)))))))))
  all_goals simp [step, cfg, execInstr, readRegs]

theorem loop_trace (xs : List (Bool × Bool)) (out : List Bool) (a s v p t : Bool) :
    Trace program (6 * xs.length + 9) (cfg (some 1) a s v p t (encodePairs xs) out)
      (cfg none false false false false false [] ((a || evalPairs xs) :: out)) := by
  induction xs generalizing a s v p t with
  | nil => simpa [evalPairs, encodePairs] using finish a s v p t out
  | cons x xs ih =>
    rcases x with ⟨sign, value⟩
    have h := (cycle a s v p t sign value (encodePairs xs) out).trans
      (ih (a || truth sign value) sign value true (truth sign value))
    convert h using 1 <;> simp [evalPairs, encodePairs, List.length_cons, Bool.or_assoc] ; omega

theorem trace (xs : List (Bool × Bool)) :
    Trace program (6 * xs.length + 10) (initial program (encodePairs xs))
      (terminal program [evalPairs xs]) := by
  have hstart : step program (cfg (some 0) false false false false false (encodePairs xs) []) =
      some (cfg (some 1) false false false false false (encodePairs xs) []) := by
    simp [step, cfg, execInstr]
  have h := Computation.Trace.cons hstart (loop_trace xs [] false false false false false)
  have hr : regs false false false false false = fun _ => false := by funext i; simp [regs]
  have hi : cfg (some 0) false false false false false (encodePairs xs) [] =
      initial program (encodePairs xs) := by
    simp [initial, cfg, hr ]
    rfl
  have ht : cfg none false false false false false [] [evalPairs xs] =
      terminal program [evalPairs xs] := by
    simp only [cfg, terminal, hr]
    congr 1
    funext i
    fin_cases i <;> rfl
  simpa only [Bool.false_or, hi, ht, Nat.add_assoc] using h

theorem primitive_outputs (xs : List (Bool × Bool)) :
    (BitProgram.primitive program).OutputsInTime (encodePairs xs) (evalPairs xs)
      (BitProgram.primitiveOverhead program * (6 * xs.length + 10)) :=
  BitProgram.primitive_outputs program ⟨_, le_rfl, trace xs⟩

/-- The actual fixed program computes clause truth once the caller supplies
the sign/value row stream, including the empty-clause case. -/
theorem primitive_clause {V : Type*} [DecidableEq V]
    (a : SAT.Assignment V) (ls : List (SAT.Literal V)) (C : SAT.Clause V)
    (hls : ls.toFinset = C) :
    (BitProgram.primitive program).OutputsInTime
      (encodePairs (ls.map fun l => (l.positive, a l.variable))) (C.eval a)
      (BitProgram.primitiveOverhead program * (6 * ls.length + 10)) := by
  simpa only [List.length_map, evalPairs_clause a ls C hls] using
    primitive_outputs (ls.map fun l => (l.positive, a l.variable))

end SignedClause

namespace UnaryValidity

open StructuredProgram (State)

abbrev inputState (label width : List Bool) : State 3 4 :=
  ⟨fun _ => false, fun i => if i = 0 then label else if i = 2 then width else []⟩

abbrev skipProgram : Program 3 4 7 := ArrayPrograms.countedSkipProgram 2 0 3 1 2

def stackPort (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩

theorem stackPort_injective : Function.Injective stackPort := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 4 => i.val) h)

abbrev command : StructuredCalls.Cmd 3 4 :=
  .seq (.call skipProgram)
    (.call (ProgramLinking.liftProgram ZeroBits.program id stackPort))

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

theorem skip_trace (low high width : List Bool) (hw : width.length = low.length) :
    Trace skipProgram (6 * low.length + 5)
      ((inputState (low ++ high) width).withPC (some skipProgram.entry))
      ((inputState high []).withPC none) := by
  have h := ArrayPrograms.countedSkipProgram_trace (2 : Fin 4) 0 3 (1 : Fin 3) 2
    (by decide) (by decide) (by decide) (by decide)
    low high width (fun _ => false) (inputState (low ++ high) width).stacks
    rfl rfl hw rfl
  have he : ArrayPrograms.countedSkipResult (6 : Fin 7) (2 : Fin 4) 0 (1 : Fin 3) 2
      high (fun _ => false) (inputState (low ++ high) width).stacks =
      (inputState high []).withPC (some (6 : Fin 7)) := by
    unfold ArrayPrograms.countedSkipResult State.withPC
    congr 1
    · funext i
      fin_cases i <;> simp [readRegs ]
    · funext i
      fin_cases i <;> simp [ArrayPrograms.countedSkipStacks ]
  have h' : Trace skipProgram (6 * low.length + 4)
      ((inputState (low ++ high) width).withPC (some skipProgram.entry))
      ((inputState high []).withPC (some 6)) := by
    simpa only [skipProgram, ArrayPrograms.countedSkipProgram, inputState,
      StructuredProgram.State.withPC, he] using h
  have hs : step skipProgram ((inputState high []).withPC (some 6)) =
      some ((inputState high []).withPC none) := by
    simp [step, execInstr, State.withPC]
  have total := h'.trans (Computation.Trace.cons hs (Computation.Trace.refl _))
  simpa only [Nat.add_assoc] using total

private theorem embed_input (high : List Bool) :
    StructuredCalls.embedState id stackPort (StructuredProgram.ioState (1 : Fin 4) [])
      (StructuredProgram.ioState (r := 3) (0 : Fin 2) high) = inputState high [] := by
  apply state_ext
  · funext i
    simpa [inputState, StructuredProgram.ioState] using
      StructuredCalls.embedState_register id stackPort
        (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
        (StructuredProgram.ioState (r := 3) (0 : Fin 2) high) Function.injective_id i
  · funext i
    fin_cases i
    · simpa [stackPort, inputState, StructuredProgram.ioState] using
        StructuredCalls.embedState_stack id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (0 : Fin 2) high) stackPort_injective (0 : Fin 2)
    · simpa [stackPort, inputState, StructuredProgram.ioState] using
        StructuredCalls.embedState_stack id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (0 : Fin 2) high) stackPort_injective (1 : Fin 2)
    · simpa [inputState, StructuredProgram.ioState] using
        StructuredCalls.embedState_stack_frame id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (0 : Fin 2) high) (2 : Fin 4) (by decide)
    · simpa [inputState, StructuredProgram.ioState] using
        StructuredCalls.embedState_stack_frame id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (0 : Fin 2) high) (3 : Fin 4) (by decide)

private theorem embed_output (answer : Bool) :
    StructuredCalls.embedState id stackPort (StructuredProgram.ioState (1 : Fin 4) [])
      (StructuredProgram.ioState (r := 3) (1 : Fin 2) [answer]) =
      StructuredProgram.ioState (r := 3) (1 : Fin 4) [answer] := by
  apply state_ext
  · funext i
    simpa [StructuredProgram.ioState] using
      StructuredCalls.embedState_register id stackPort
        (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
        (StructuredProgram.ioState (r := 3) (1 : Fin 2) [answer]) Function.injective_id i
  · funext i
    fin_cases i
    · simpa [stackPort, StructuredProgram.ioState] using
        StructuredCalls.embedState_stack id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (1 : Fin 2) [answer]) stackPort_injective (0 : Fin 2)
    · simpa [stackPort, StructuredProgram.ioState] using
        StructuredCalls.embedState_stack id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (1 : Fin 2) [answer]) stackPort_injective (1 : Fin 2)
    · simpa [StructuredProgram.ioState] using
        StructuredCalls.embedState_stack_frame id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (1 : Fin 2) [answer]) (2 : Fin 4) (by decide)
    · simpa [StructuredProgram.ioState] using
        StructuredCalls.embedState_stack_frame id stackPort
          (StructuredProgram.ioState (r := 3) (1 : Fin 4) [])
          (StructuredProgram.ioState (r := 3) (1 : Fin 2) [answer]) (3 : Fin 4) (by decide)

/-- Actual unary validity evaluation. The width is data on a separate unary
counter stack; the label is a padded little-endian bit word. -/
theorem eval (low high width : List Bool) (hw : width.length = low.length) :
    StructuredCalls.Eval command (6 * low.length + 4 * high.length + 13)
      (inputState (low ++ high) width)
      (StructuredProgram.ioState (1 : Fin 4) [allZero high]) := by
  have hs : StructuredCalls.Eval (.call skipProgram) (6 * low.length + 5)
      (inputState (low ++ high) width) (inputState high []) :=
    .call skipProgram (skip_trace low high width hw)
  have hz := StructuredCalls.eval_call_lifted ZeroBits.program id stackPort
    (StructuredProgram.ioState (r := 3) (1 : Fin 4) []) Function.injective_id stackPort_injective
    (a := StructuredProgram.ioState (0 : Fin 2) high)
    (b := StructuredProgram.ioState (1 : Fin 2) [allZero high]) (ZeroBits.trace high)
  rw [embed_input, embed_output] at hz
  have total := StructuredCalls.Eval.seq hs hz
  convert total using 1 ; omega

abbrev program : Program 3 4 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 1

theorem control_size : StructuredCalls.size command + 1 = 18 := rfl

theorem trace (low high width : List Bool) (hw : width.length = low.length) :
    Trace program (6 * low.length + 4 * high.length + 14)
      ((inputState (low ++ high) width).withPC (some program.entry))
      ((StructuredProgram.ioState (1 : Fin 4) [allZero high]).withPC none) := by
  simpa only [Nat.add_assoc] using StructuredCalls.compiled_halt_trace (eval low high width hw) 0 1

theorem primitive_execution (low high width : List Bool) (hw : width.length = low.length) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (6 * low.length + 4 * high.length + 14))
      (BitProgram.primitiveCfg program
        ((inputState (low ++ high) width).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((StructuredProgram.ioState (1 : Fin 4) [allZero high]).withPC none)) :=
  BitProgram.primitive_trace program (trace low high width hw)

theorem result_correct (low high : List Bool) :
    allZero high = decide (BinaryArithmetic.toNat (low ++ high) < 2 ^ low.length) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using unary_validity_iff low high

end UnaryValidity

section FactorSemantics

variable {V J : Type*} [DecidableEq V] [DecidableEq J] {b : J → ℕ}

omit [DecidableEq V] in
/-- The numeric predicate computed by the unary program is exactly the
constructed prime-label factor's acceptance condition. -/
theorem unary_matches_factor {p : ℕ} [NeZero p]
    (positions : V ≃ (j : J) × Fin (b j)) (capacity : ∀ j, 2 ^ b j ≤ p)
    (F : SAT.CNF V) (x : J → ZMod p) (j : J) (low high : List Bool)
    (hlen : low.length = b j) (hbits : BinaryArithmetic.toNat (low ++ high) = (x j).val) :
    allZero high = true ↔
      Factor.evalFactor (FactorReduction.primeLabelCNF positions capacity F) (.inl j) x = true := by
  have hz := unary_validity_iff low high
  rw [hlen, hbits] at hz
  exact hz.trans (FactorReduction.primeLabelCNF_unary_iff positions capacity F x j).symm

/-- On a valid encoded row, the finite source search returns the source table
value. This is semantic justification, not a unit-cost execution premise. -/
theorem factorTable_on_encoding {E A : Type*} [DecidableEq A]
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (scope : E → Finset J)
    (table : (e : E) → FactorReduction.LocalAssignment
      (fun j => Fin (b j) → Bool) (scope e) → Bool)
    (e : E) (vals : FactorReduction.LocalAssignment (fun j => Fin (b j) → Bool) (scope e)) :
    FactorReduction.factorTable enc scope table (.inr e)
      (fun j => enc j.val (vals j)) = table e vals := by
  apply Bool.eq_iff_iff.mpr
  simp only [FactorReduction.factorTable, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, he⟩
    have heq : w = vals := by
      funext j
      exact (enc j.val).injective (he j)
    simpa only [heq] using hw
  · intro h
    exact ⟨vals, h, fun _ => rfl⟩

/-- The signed-bit program computes an actual constructed clause factor on
valid encoded labels. The input stream consists of the explicitly supplied
decoded values for that clause's literals. -/
theorem primitive_clause_factor {A : Type*} [DecidableEq A]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V)
    (C : {C // C ∈ F}) (x : (j : J) → Fin (b j) → Bool)
    (ls : List (SAT.Literal V)) (hls : ls.toFinset = C.val) :
    (BitProgram.primitive SignedClause.program).OutputsInTime
      (SignedClause.encodePairs (ls.map fun l =>
        (l.positive, FactorReduction.assignmentFromChunks positions x l.variable)))
      (Factor.evalFactor (FactorReduction.cnfFactorSystem positions enc F) (.inr C)
        (FactorReduction.encode enc x))
      (BitProgram.primitiveOverhead SignedClause.program * (6 * ls.length + 10)) := by
  have hf : Factor.evalFactor (FactorReduction.cnfFactorSystem positions enc F) (.inr C)
      (FactorReduction.encode enc x) =
      FactorReduction.cnfTable positions F C (fun j => x j.val) :=
    factorTable_on_encoding enc (FactorReduction.cnfScope positions F)
      (FactorReduction.cnfTable positions F) C (fun j => x j.val)
  have ht : FactorReduction.cnfTable positions F C (fun j => x j.val) =
      C.val.eval (FactorReduction.assignmentFromChunks positions x) :=
    Bool.eq_iff_iff.mpr (FactorReduction.cnfTable_true_iff positions F C x)
  rw [hf, ht]
  exact SignedClause.primitive_clause (FactorReduction.assignmentFromChunks positions x) ls C.val hls

end FactorSemantics

end SubexponentialSAT.SubexpFactorProgram

end OAI.Algorithms
