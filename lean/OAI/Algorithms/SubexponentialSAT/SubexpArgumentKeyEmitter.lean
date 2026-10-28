import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentKeyProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpArgumentKeyEmitter

open BitProgram StructuredCalls SubexpArgumentKeyProgram

/-- A verified bit-emission effect. This is used only to compose measured
executions of the concrete commands below. -/
abbrev Emits (command : Cmd 4 5) (cost : ℕ) (bits : List Bool)
    (mark u : Bool) (before after : Fin 3 → List Bool) : Prop :=
  ∀ v p width output, ∃ v' p', Eval command cost
    (state v p mark u before width output)
    (state v' p' mark u after (width.drop bits.length) (bits.reverse ++ output))

theorem Emits.seq {first second : Cmd 4 5} {n m : ℕ} {left right : List Bool}
    {mark u : Bool} {a b c : Fin 3 → List Bool}
    (hfirst : Emits first n left mark u a b) (hsecond : Emits second m right mark u b c) :
    Emits (.seq first second) (n + m) (left ++ right) mark u a c := by
  intro v p width output
  obtain ⟨v₁, p₁, h₁⟩ := hfirst v p width output
  obtain ⟨v₂, p₂, h₂⟩ := hsecond v₁ p₁ (width.drop left.length) (left.reverse ++ output)
  refine ⟨v₂, p₂, ?_⟩
  simpa only [List.length_append, List.drop_drop, List.reverse_append, List.append_assoc] using
    Eval.seq h₁ h₂

theorem emits_repeat (i : Fin 3) (b mark u : Bool) (counts : Fin 3 → List Bool) :
    Emits (repeatBit i b) (5 * (counts i).length + 2)
      (List.replicate (counts i).length b) mark u counts (Function.update counts i []) := by
  intro v p width output
  refine ⟨false, false, ?_⟩
  simpa using repeatBit_eval i b v p mark u counts width output

/-- Only fixed literal fragments of length at most two are used by the key
program. Runtime exponents are processed by the counter loops. -/
def literal : List Bool → Cmd 4 5
  | [] => .base .skip
  | b :: bs => .seq (emitBit b) (literal bs)

theorem emits_literal (bits : List Bool) (mark u : Bool) (counts : Fin 3 → List Bool) :
    Emits (literal bits) (3 * bits.length) bits mark u counts counts := by
  induction bits with
  | nil =>
    intro v p width output
    exact ⟨v, p, .base (.skip _)⟩
  | cons b bits ih =>
    have hb : Emits (emitBit b) 3 [b] mark u counts counts := by
      intro v p width output
      refine ⟨width.head?.getD false, width.head?.isSome, ?_⟩
      simpa using emitBit_eval b v p mark u counts width output
    have h := hb.seq ih
    have hn : 3 + 3 * bits.length = 3 * (b :: bits).length := by simp; omega
    simpa only [literal, List.singleton_append, hn] using h

def markBits (mark : Bool) : List Bool := if mark then [true, false] else []
def uBits (u : Bool) : List Bool := if u then [true] else []

abbrev emitMark : Cmd 4 5 := .ite 2 (literal [true, false]) (literal [])
abbrev emitU : Cmd 4 5 := .ite 3 (literal [true]) (literal [])

theorem emits_mark (mark u : Bool) (counts : Fin 3 → List Bool) :
    Emits emitMark (3 * (markBits mark).length + 1) (markBits mark) mark u counts counts := by
  intro v p width output
  cases mark with
  | false =>
    refine ⟨v, p, ?_⟩
    exact Eval.ite_false rfl (.base (.skip _))
  | true =>
    obtain ⟨v', p', h⟩ := emits_literal [true, false] true u counts v p width output
    exact ⟨v', p', Eval.ite_true rfl h⟩

theorem emits_u (mark u : Bool) (counts : Fin 3 → List Bool) :
    Emits emitU (3 * (uBits u).length + 1) (uBits u) mark u counts counts := by
  intro v p width output
  cases u with
  | false =>
    refine ⟨v, p, ?_⟩
    exact Eval.ite_false rfl (.base (.skip _))
  | true =>
    obtain ⟨v', p', h⟩ := emits_literal [true] mark true counts v p width output
    exact ⟨v', p', Eval.ite_true rfl h⟩

def rawKey (left right z : ℕ) (mark u : Bool) : List Bool :=
  List.replicate left false ++ (markBits mark ++ (List.replicate right false ++
    (uBits u ++ ([false] ++ (List.replicate z true ++ [false])))))

def rawCost (left right z : ℕ) (mark u : Bool) : ℕ :=
  (5 * left + 2) + ((3 * (markBits mark).length + 1) + ((5 * right + 2) +
    ((3 * (uBits u).length + 1) + (3 + ((5 * z + 2) + 3)))))

abbrev rawCommand : Cmd 4 5 :=
  .seq (repeatBit 0 false) (.seq emitMark (.seq (repeatBit 1 false)
    (.seq emitU (.seq (literal [false]) (.seq (repeatBit 2 true) (literal [false]))))))

def counters (left right z : ℕ) : Fin 3 → List Bool :=
  SubexpPostfixControl.triple (List.replicate left true)
    (List.replicate right true) (List.replicate z true)

theorem rawCommand_emits (left right z : ℕ) (mark u : Bool) :
    Emits rawCommand (rawCost left right z mark u) (rawKey left right z mark u)
      mark u (counters left right z) (counters 0 0 0) := by
  let a := counters left right z
  let b := Function.update a 0 []
  let c := Function.update b 1 []
  let d := Function.update c 2 []
  have h := (emits_repeat 0 false mark u a).seq
    ((emits_mark mark u b).seq ((emits_repeat 1 false mark u b).seq
      ((emits_u mark u c).seq ((emits_literal [false] mark u c).seq
        ((emits_repeat 2 true mark u c).seq (emits_literal [false] mark u d))))))
  simpa [rawCommand, rawCost, rawKey, a, b, c, d, counters,
    SubexpPostfixControl.triple] using h

abbrev padLoop : Cmd 4 5 := .while 1 (emitBit false)
abbrev pad : Cmd 4 5 := .seq (atom (.pop 3 0 1)) padLoop

theorem padLoop_eval (word : List Bool) (mark u : Bool)
    (counts : Fin 3 → List Bool) (output : List Bool) :
    Eval padLoop (4 * word.length + 1)
      (state (word.head?.getD false) word.head?.isSome mark u counts word.tail output)
      (state false false mark u counts [] (List.replicate word.length false ++ output)) := by
  induction word generalizing output with
  | nil => exact .while_false rfl
  | cons b word ih =>
    have h := Eval.while_true (test := (1 : Fin 4)) rfl
      (emitBit_eval false b true mark u counts word (output)) (ih (false :: output))
    have ho : List.replicate word.length false ++ false :: output =
        List.replicate (word.length + 1) false ++ output := by
      simp [List.replicate_succ', List.append_assoc]
    have hn : 3 + (4 * word.length + 1) + 1 = 4 * (b :: word).length + 1 := by simp; omega
    simpa only [padLoop, List.head?_cons, Option.getD_some, Option.isSome_some,
      List.tail_cons, List.length_cons, ho, hn] using h

theorem pad_eval (v p mark u : Bool) (counts : Fin 3 → List Bool) (width output : List Bool) :
    Eval pad (4 * width.length + 2) (state v p mark u counts width output)
      (state false false mark u counts [] (List.replicate width.length false ++ output)) := by
  have hp : Eval (atom (.pop 3 0 1)) 1 (state v p mark u counts width output)
      (state (width.head?.getD false) width.head?.isSome mark u counts width.tail output) := by
    have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (3 : Fin 5) (0 : Fin 4) 1)
      (state v p mark u counts width output)
    apply Eval.base
    simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
      state, regs, readRegs, SubexpPostfixControl.quadruple, update_width] using h
  have h := Eval.seq hp (padLoop_eval width mark u counts output)
  have hn : 1 + (4 * width.length + 1) = 4 * width.length + 2 := by omega
  simpa only [pad, hn] using h

abbrev command : Cmd 4 5 := .seq rawCommand pad
def program := StructuredCalls.compiled command 0 4

def paddedKey (left right z B : ℕ) (mark u : Bool) : List Bool :=
  rawKey left right z mark u ++
    List.replicate (B - (rawKey left right z mark u).length) false

theorem command_eval (left right z B : ℕ) (v p mark u : Bool) (output : List Bool) :
    Eval command
      (rawCost left right z mark u + 4 * (B - (rawKey left right z mark u).length) + 2)
      (state v p mark u (counters left right z) (List.replicate B true) output)
      (state false false mark u (counters 0 0 0) []
        ((paddedKey left right z B mark u).reverse ++ output)) := by
  obtain ⟨v', p', hr⟩ := rawCommand_emits left right z mark u v p (List.replicate B true) output
  have hp := pad_eval v' p' mark u (counters 0 0 0)
    ((List.replicate B true).drop (rawKey left right z mark u).length)
    ((rawKey left right z mark u).reverse ++ output)
  have h := Eval.seq hr hp
  simpa [command, paddedKey, List.reverse_append, List.append_assoc, Nat.add_assoc] using h

theorem program_trace (left right z B : ℕ) (v p mark u : Bool) (output : List Bool) :
    Trace program
      (rawCost left right z mark u + 4 * (B - (rawKey left right z mark u).length) + 3)
      ((state v p mark u (counters left right z) (List.replicate B true) output).withPC
        (some program.entry))
      ((state false false mark u (counters 0 0 0) []
        ((paddedKey left right z B mark u).reverse ++ output)).withPC none) := by
  simpa only [program, Nat.add_assoc] using
    StructuredCalls.compiled_halt_trace (command_eval left right z B v p mark u output) 0 4

private theorem flatMap_zero (D : ℕ) :
    (List.replicate D 0).flatMap SymbolicCost.unaryWord = List.replicate D false := by
  induction D with
  | zero => rfl
  | succ D ih => simp [List.replicate_succ, SymbolicCost.unaryWord, ih]

private theorem ofFn_point {D : ℕ} (i : Fin D) :
    (List.ofFn (fun w : Fin D => if w = i then 1 else 0)) =
      List.replicate i.val 0 ++ 1 :: List.replicate (D - i.val - 1) 0 := by
  induction D with
  | zero => exact Fin.elim0 i
  | succ D ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [List.ofFn_succ, List.ofFn_const]
    · simp [List.ofFn_succ, ih j, List.replicate_succ]
      exact Ne.symm (Fin.succ_ne_zero j)

theorem rawKey_constant (D z : ℕ) (u : Bool) :
    rawKey D 0 z false u =
      SymbolicCost.encodeIndex (SubexpArgumentCode.constantIndex D (if u then 1 else 0) z) := by
  cases u <;> simp [rawKey, markBits, uBits, SymbolicCost.encodeIndex, SymbolicCost.indexData,
    SubexpArgumentCode.constantIndex, List.ofFn_const, SymbolicCost.unaryWords,
    flatMap_zero, SymbolicCost.unaryWord]

theorem rawKey_coordinate {D : ℕ} (i : Fin D) (z : ℕ) (u : Bool) :
    rawKey i.val (D - i.val - 1) z true u =
      SymbolicCost.encodeIndex (SubexpArgumentCode.coordinateIndex i (if u then 1 else 0) z) := by
  cases u <;> simp [rawKey, markBits, uBits, SymbolicCost.encodeIndex, SymbolicCost.indexData,
    SubexpArgumentCode.coordinateIndex, ofFn_point, SymbolicCost.unaryWords,
    flatMap_zero, SymbolicCost.unaryWord, List.append_assoc]

theorem paddedKey_constant (D z : ℕ) (u : Bool) :
    paddedKey D 0 z (SubexpSymbolicCost.indexBits D) false u =
      SubexpSymbolicCost.fixedKey
        (SubexpArgumentCode.constantIndex D (if u then 1 else 0) z) := by
  rw [paddedKey, rawKey_constant]
  rfl

theorem paddedKey_coordinate {D : ℕ} (i : Fin D) (z : ℕ) (u : Bool) :
    paddedKey i.val (D - i.val - 1) z (SubexpSymbolicCost.indexBits D) true u =
      SubexpSymbolicCost.fixedKey
        (SubexpArgumentCode.coordinateIndex i (if u then 1 else 0) z) := by
  rw [paddedKey, rawKey_coordinate]
  rfl

theorem program_constant_trace (D z : ℕ) (v p u : Bool) (output : List Bool) :
    Trace program
      (rawCost D 0 z false u + 4 * (SubexpSymbolicCost.indexBits D - (rawKey D 0 z false u).length) + 3)
      ((state v p false u (counters D 0 z)
        (List.replicate (SubexpSymbolicCost.indexBits D) true) output).withPC (some program.entry))
      ((state false false false u (counters 0 0 0) []
        ((SubexpSymbolicCost.fixedKey
          (SubexpArgumentCode.constantIndex D (if u then 1 else 0) z)).reverse ++ output)).withPC none) := by
  simpa only [paddedKey_constant] using
    program_trace D 0 z (SubexpSymbolicCost.indexBits D) v p false u output

theorem program_coordinate_trace {D : ℕ} (i : Fin D) (z : ℕ) (v p u : Bool) (output : List Bool) :
    Trace program
      (rawCost i.val (D - i.val - 1) z true u +
        4 * (SubexpSymbolicCost.indexBits D - (rawKey i.val (D - i.val - 1) z true u).length) + 3)
      ((state v p true u (counters i.val (D - i.val - 1) z)
        (List.replicate (SubexpSymbolicCost.indexBits D) true) output).withPC (some program.entry))
      ((state false false true u (counters 0 0 0) []
        ((SubexpSymbolicCost.fixedKey
          (SubexpArgumentCode.coordinateIndex i (if u then 1 else 0) z)).reverse ++ output)).withPC none) := by
  simpa only [paddedKey_coordinate] using
    program_trace i.val (D - i.val - 1) z (SubexpSymbolicCost.indexBits D) v p true u output

theorem rawCost_le (left right z : ℕ) (mark u : Bool) :
    rawCost left right z mark u ≤ 5 * (rawKey left right z mark u).length + 4 := by
  cases mark <;> cases u <;>
    simp [rawCost, rawKey, markBits, uBits] <;> omega

theorem program_steps_le (left right z B : ℕ) (mark u : Bool)
    (hwidth : (rawKey left right z mark u).length ≤ B) :
    rawCost left right z mark u + 4 * (B - (rawKey left right z mark u).length) + 3 ≤ 9 * B + 7 := by
  have h := rawCost_le left right z mark u
  omega

end SubexponentialSAT.SubexpArgumentKeyEmitter

end OAI.Algorithms
