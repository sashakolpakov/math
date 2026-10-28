import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableStep

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Pairs (B : ℕ) := List (Word B × Word B)

abbrev outputBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → List Bool
  | [], _ => []
  | (c,a) :: pairs, previous =>
    (coefficient p t M tail c minusOne previous).val ++ outputBits p t M tail minusOne pairs a

abbrev lastPrevious {B : ℕ} : Pairs B → Word B → Word B
  | [], previous => previous
  | (_,a) :: pairs, _ => lastPrevious pairs a

abbrev lastProduced (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → List Bool → List Bool
  | [], _, initial => initial
  | (c,a) :: pairs, previous, _ =>
    lastProduced p t M tail minusOne pairs a (coefficient p t M tail c minusOne previous).val

abbrev popCount : Cmd 8 27 := .base (.atom (.pop 11 1 3))
abbrev coefficientLoop : Cmd 8 27 := .while 3 (.seq coefficientStep popCount)
abbrev coefficientScan : Cmd 8 27 := .seq popCount coefficientLoop

theorem popCount_eval (s : Store) (regs : Fin 8 → Bool) :
    Eval popCount 1 (state regs s)
      (state (readRegs regs 1 3 s.count.head?) {s with count := s.count.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 27) 11 1 3)
    (state regs s) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, tapes]

private theorem loop_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = pairs.length) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hnew : s.newTail.length ≤ baseWidth p t) :
    ∃ n ≤ pairs.length * (18000*(baseWidth p t+1)^2+102*baseWidth p t+90)+1, ∃ rf,
      Eval coefficientLoop n
        (state (readRegs regs 1 3 count.head?) {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count.tail})
        (state rf {s with left := (lastPrevious pairs previous).val, source := [], saved := [], vector := [], coefficients := [], tail := tail.val, minusOne := minusOne.val, count := [], newTail := lastProduced p t M tail minusOne pairs previous s.newTail, output := (outputBits p t M tail minusOne pairs previous).reverse ++ s.output}) := by
  induction pairs generalizing previous s regs count with
  | nil =>
    have hc : count = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
    subst count
    refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
    simpa [coefficientLoop, lastPrevious, lastProduced, outputBits,
      RingScan.rightBits, RingScan.leftBits] using
      (Eval.while_false (body := .seq coefficientStep popCount)
        (show (state (readRegs regs 1 3 none)
            { s with
              left := previous.val
              source := []
              saved := []
              vector := (List.nil : List Bool)
              coefficients := (List.nil : List Bool)
              tail := tail.val
              minusOne := minusOne.val
              count := [] }).regs 3 = false by
          simp [ readRegs_present]))
  | cons pair pairs ih =>
    cases count with
    | nil => simp at hcount
    | cons bit count =>
      have hc : count.length = pairs.length := by simpa using hcount
      let z := coefficient p t M tail pair.1 minusOne previous
      let s' := {s with newTail := z.val, output := z.val.reverse ++ s.output}
      obtain ⟨n, hn, rf, hs⟩ := coefficientStep_eval p t M {s with count := count}
        (readRegs regs 1 3 (some bit)) tail pair.1 minusOne previous pair.2
        (RingScan.leftBits pairs) (RingScan.rightBits pairs) hmod hw hnew
      have hp := popCount_eval
        {s' with left := pair.2.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count} rf
      obtain ⟨m, hm, rg, hl⟩ := ih pair.2 s' rf count hc hmod hw
        (by simpa [s'] using z.property.le)
      have he := Eval.while_true
        (show (state (readRegs regs 1 3 (some bit)) {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits (pair::pairs), coefficients := RingScan.leftBits (pair::pairs), tail := tail.val, minusOne := minusOne.val, count := count}).regs 3 = true by
          simp [ readRegs_present])
        (hs.seq hp) hl
      refine ⟨n+1+m+1, ?_, rg, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simpa only [coefficientLoop, outputBits, lastPrevious, lastProduced, RingScan.leftBits,
          RingScan.rightBits, List.head?_cons, List.tail_cons, List.reverse_append,
          List.append_assoc, s', z] using he

theorem coefficientScan_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t))
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = pairs.length) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hnew : s.newTail.length ≤ baseWidth p t) :
    ∃ n ≤ pairs.length * (18000*(baseWidth p t+1)^2+102*baseWidth p t+90)+2, ∃ rf,
      Eval coefficientScan n
        (state regs {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count})
        (state rf {s with left := (lastPrevious pairs previous).val, source := [], saved := [], vector := [], coefficients := [], tail := tail.val, minusOne := minusOne.val, count := [], newTail := lastProduced p t M tail minusOne pairs previous s.newTail, output := (outputBits p t M tail minusOne pairs previous).reverse ++ s.output}) := by
  have hp := popCount_eval {s with left := previous.val, source := [], saved := [], vector := RingScan.rightBits pairs, coefficients := RingScan.leftBits pairs, tail := tail.val, minusOne := minusOne.val, count := count} regs
  obtain ⟨n, hn, rf, hl⟩ := loop_eval p t M tail minusOne pairs previous s regs count hcount hmod hw hnew
  exact ⟨1+n, by omega, rf, hp.seq hl⟩

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
