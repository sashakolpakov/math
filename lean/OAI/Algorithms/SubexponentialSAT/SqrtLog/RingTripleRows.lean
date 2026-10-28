import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

def leftBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | p :: ps => p.1.val ++ leftBits ps

def rightBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | p :: ps => p.2.val ++ rightBits ps

def rowBits {B : ℕ} (x : List Bool) : List (Word B × Word B) → List Bool
  | [] => []
  | p :: ps => (x ++ p.1.val ++ p.2.val) ++ rowBits x ps

theorem leftBits_length {B : ℕ} (ps : List (Word B × Word B)) :
    (leftBits ps).length = ps.length * B := by
  induction ps with
  | nil => simp [leftBits]
  | cons p ps ih =>
      simp only [leftBits, List.length_append, ih, List.length_cons, Nat.add_mul]
      rw [p.1.property]
      omega

abbrev popJ : Cmd 2 16 := .base (.atom (.pop 12 0 1))
abbrev jLoop : Cmd 2 16 := .while 1 (.seq emitTriple popJ)
abbrev jScan : Cmd 2 16 := .seq popJ jLoop

theorem popJ_eval (regs : Fin 2 → Bool) (s : Store) :
    Eval popJ 1 (state regs s)
      (state (readRegs regs 0 1 s.jc.head?) {s with jc := s.jc.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 16) 12 0 1)
    (state regs s) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, tapes]

theorem jLoop_eval (B : ℕ) (s : Store) (pairs : List (Word B × Word B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = pairs.length) (hx : s.held.length = B) (hw : s.width.length = B) :
    ∃ n ≤ pairs.length * (44 * B + 40) + 1, ∃ regs',
      Eval jLoop n
        (state (readRegs regs 0 1 count.head?) {s with ys := leftBits pairs, table := rightBits pairs ++ tail, jc := count.tail})
        (state regs' {s with ys := [], table := tail, out := (rowBits s.held pairs).reverse ++ s.out, jc := []}) := by
  induction pairs generalizing s count regs with
  | nil =>
    have hcount : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
    subst count
    refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
    simpa [leftBits, rightBits, rowBits] using
      (Eval.while_false (test := (1 : Fin 2)) (body := .seq emitTriple popJ)
        (a := state (readRegs regs 0 1 none)
          {s with ys := [], table := tail, jc := []}) (by simp [state, readRegs_present]))
  | cons p pairs ih =>
    cases count with
    | nil => simp at hc
    | cons bit count =>
      have hc' : count.length = pairs.length := by simpa using hc
      obtain ⟨r₁, hemit⟩ := emitTriple_eval B {s with jc := count}
        (readRegs regs 0 1 (some bit)) p.1.val p.2.val (leftBits pairs)
        (rightBits pairs ++ tail) hx p.1.property p.2.property hw
      let m := {s with ys := leftBits pairs, table := rightBits pairs ++ tail, out := (s.held ++ p.1.val ++ p.2.val).reverse ++ s.out, jc := count}
      have hp := popJ_eval r₁ m
      obtain ⟨n, hn, r₂, hloop⟩ := ih m count r₁ hc' hx hw
      have hbody : Eval (.seq emitTriple popJ) (44 * B + 38 + 1)
          (state (readRegs regs 0 1 (some bit))
            {s with ys := leftBits (p :: pairs), table := rightBits (p :: pairs) ++ tail, jc := count})
          (state (readRegs r₁ 0 1 count.head?) {m with jc := count.tail}) := by
        simpa [m, leftBits, rightBits, List.append_assoc] using hemit.seq hp
      refine ⟨(44 * B + 38) + 1 + n + 1, ?_, r₂, ?_⟩
      · simp only [List.length_cons]; nlinarith
      · have he := Eval.while_true
          (test := (1 : Fin 2))
          (show (state (readRegs regs 0 1 (some bit))
            {s with ys := leftBits (p :: pairs), table := rightBits (p :: pairs) ++ tail, jc := count}).regs 1 = true by simp [state, readRegs_present])
          hbody hloop
        simpa [jLoop, m, leftBits, rightBits, rowBits,
          List.reverse_append, List.append_assoc] using he

theorem jScan_eval (B : ℕ) (s : Store) (pairs : List (Word B × Word B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = pairs.length) (hx : s.held.length = B) (hw : s.width.length = B) :
    ∃ n ≤ pairs.length * (44 * B + 40) + 2, ∃ regs',
      Eval jScan n
        (state regs {s with ys := leftBits pairs, table := rightBits pairs ++ tail, jc := count})
        (state regs' {s with ys := [], table := tail, out := (rowBits s.held pairs).reverse ++ s.out, jc := []}) := by
  have hp := popJ_eval regs {s with ys := leftBits pairs, table := rightBits pairs ++ tail, jc := count}
  obtain ⟨n, hn, regs', ht⟩ := jLoop_eval B s pairs tail count regs hc hx hw
  exact ⟨1 + n, by omega, regs', hp.seq ht⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
