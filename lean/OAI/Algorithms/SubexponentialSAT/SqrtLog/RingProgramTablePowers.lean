import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableRound

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def iterData (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (zeroWord minusOne : Word (baseWidth p t)) {d : ℕ}
    (c : List.Vector (Word (baseWidth p t)) d) : ℕ → VectorData (baseWidth p t) d → VectorData (baseWidth p t) d
  | 0, v => v
  | n+1, v => iterData p t M zeroWord minusOne c n (advance p t M zeroWord minusOne c v)

def generatedBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (zeroWord minusOne : Word (baseWidth p t)) {d : ℕ}
    (c : List.Vector (Word (baseWidth p t)) d) : ℕ → VectorData (baseWidth p t) d → List Bool
  | 0, _ => []
  | n+1, v =>
    let next := advance p t M zeroWord minusOne c v
    wordBits next.coefficients.val ++ generatedBits p t M zeroWord minusOne c n next

abbrev popRound : Cmd 8 27 := .base (.atom (.pop 26 1 3))
abbrev powerLoop : Cmd 8 27 := .while 3 (.seq round popRound)
abbrev powerScan : Cmd 8 27 := .seq popRound powerLoop

theorem popRound_eval (s : Store) (regs : Fin 8 → Bool) :
    Eval popRound 1 (state regs s)
      (state (readRegs regs 1 3 s.rounds.head?) {s with rounds := s.rounds.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 27) 26 1 3)
    (state regs s) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, tapes]

private theorem powerLoop_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ)
    (v : VectorData (baseWidth p t) d) (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ m ≤ n*(roundBudget (baseWidth p t) d+2)+1, ∃ rf, Eval powerLoop m
      (state (readRegs regs 1 3 count.head?) (ready {s with rounds := count.tail} c v zeroWord minusOne))
      (state rf (ready {s with rounds := [], powers := (generatedBits p t M zeroWord minusOne c n v).reverse ++ s.powers}
        c (iterData p t M zeroWord minusOne c n v) zeroWord minusOne)) := by
  induction n generalizing v s regs count with
  | zero =>
    have hc : count = [] := List.length_eq_zero_iff.mp hcount
    subst count
    refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
    apply Eval.while_false
    simp [ readRegs_present]
  | succ n ih =>
    cases count with
    | nil => simp at hcount
    | cons bit count =>
      have hc : count.length = n := by simpa using hcount
      let next := advance p t M zeroWord minusOne c v
      let s' := {s with powers := (wordBits next.coefficients.val).reverse ++ s.powers}
      obtain ⟨m, hm, rf, hr⟩ := round_eval p t M hd zeroWord minusOne c v {s with rounds := count}
        (readRegs regs 1 3 (some bit)) hmod hw hdegree
      have hp := popRound_eval (ready {s' with rounds := count} c next zeroWord minusOne) rf
      obtain ⟨k, hk, rg, hl⟩ := ih next s' rf count hc hmod hw hdegree
      have he := Eval.while_true
        (show (state (readRegs regs 1 3 (some bit)) (ready {s with rounds := count} c v zeroWord minusOne)).regs 3 = true by
          simp [ readRegs_present]) (hr.seq hp) hl
      refine ⟨m+1+k+1, ?_, rg, ?_⟩
      · nlinarith
      · simpa only [powerLoop, generatedBits, iterData, List.head?_cons, List.tail_cons,
          List.reverse_append, List.append_assoc, s', next] using he

theorem powerScan_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ)
    (v : VectorData (baseWidth p t) d) (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ m ≤ n*(roundBudget (baseWidth p t) d+2)+2, ∃ rf, Eval powerScan m
      (state regs (ready {s with rounds := count} c v zeroWord minusOne))
      (state rf (ready {s with rounds := [], powers := (generatedBits p t M zeroWord minusOne c n v).reverse ++ s.powers}
        c (iterData p t M zeroWord minusOne c n v) zeroWord minusOne)) := by
  have hp := popRound_eval (ready {s with rounds := count} c v zeroWord minusOne) regs
  obtain ⟨m, hm, rf, hl⟩ := powerLoop_eval p t M hd zeroWord minusOne c n v s regs count hcount hmod hw hdegree
  exact ⟨1+m, by omega, rf, hp.seq hl⟩

@[simp] theorem generatedBits_length (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ) (v : VectorData (baseWidth p t) d) :
    (generatedBits p t M zeroWord minusOne c n v).length = n*d*baseWidth p t := by
  induction n generalizing v with
  | zero => simp [generatedBits]
  | succ n ih => simp [generatedBits, ih]; ring

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
