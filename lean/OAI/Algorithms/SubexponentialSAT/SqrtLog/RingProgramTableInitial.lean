import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableData

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev literalStep : Cmd 8 27 :=
  .seq (clear 19) (.seq (copy 0 19) (.seq (transfer 0 20) (copy 24 0)))

theorem literalStep_eval {B : ℕ} (s : Store) (regs : Fin 8 → Bool)
    (seed zeroWord : Word B) (hnew : s.newTail.length ≤ B) :
    ∃ n ≤ 19*B+16, Eval literalStep n
      (state regs {s with left := seed.val, zero := zeroWord.val})
      (state (readRegs regs 1 3 none) {s with left := zeroWord.val, zero := zeroWord.val, newTail := seed.val, output := seed.val.reverse ++ s.output}) := by
  let s0 := {s with left := seed.val, zero := zeroWord.val}
  let s1 := {s0 with newTail := []}
  let s2 := {s1 with newTail := seed.val}
  let s3 := {s2 with left := [], output := seed.val.reverse ++ s.output}
  let s4 := {s3 with left := zeroWord.val}
  let rr := readRegs regs 1 3 none
  have h1 := clear_store_eval s0 s1 regs 19 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s1])
  have h2 := copy_store_eval s1 s2 rr 0 19 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s2, s1, s0])
  have h3 := transfer_store_eval s2 s3 rr 0 20 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s3, s2, s1, s0])
  have h4 := copy_store_eval s3 s4 rr 24 0 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s4, s3, s2, s1, s0])
  simp only [rr, readRegs_reset] at h2 h3 h4
  refine ⟨_, ?_, h1.seq (h2.seq (h3.seq h4))⟩
  simp [s0, s1, s2, s3, tapes]
  omega

abbrev literalBits {B : ℕ} : ℕ → Word B → Word B → List Bool
  | 0, _, _ => []
  | n+1, seed, zeroWord => seed.val ++ literalBits n zeroWord zeroWord

abbrev literalEnd {B : ℕ} : ℕ → Word B → Word B → Word B
  | 0, seed, _ => seed
  | n+1, _, zeroWord => literalEnd n zeroWord zeroWord

abbrev literalLast {B : ℕ} : ℕ → Word B → Word B → List Bool → List Bool
  | 0, _, _, old => old
  | n+1, seed, zeroWord, _ => literalLast n zeroWord zeroWord seed.val

abbrev literalLoop : Cmd 8 27 := .while 3 (.seq literalStep popCount)
abbrev literalScan : Cmd 8 27 := .seq popCount literalLoop

private theorem literalLoop_eval {B : ℕ} (n : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hnew : s.newTail.length ≤ B) :
    ∃ m ≤ n*(19*B+18)+1, ∃ rf, Eval literalLoop m
      (state (readRegs regs 1 3 count.head?) {s with left := seed.val, zero := zeroWord.val, count := count.tail})
      (state rf {s with left := (literalEnd n seed zeroWord).val, zero := zeroWord.val, count := [], newTail := literalLast n seed zeroWord s.newTail, output := (literalBits n seed zeroWord).reverse ++ s.output}) := by
  induction n generalizing seed s regs count with
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
      obtain ⟨m, hm, hs⟩ := literalStep_eval {s with count := count}
        (readRegs regs 1 3 (some bit)) seed zeroWord hnew
      let s' := {s with newTail := seed.val, output := seed.val.reverse ++ s.output}
      have hp := popCount_eval {s' with left := zeroWord.val, zero := zeroWord.val, count := count}
        (readRegs (readRegs regs 1 3 (some bit)) 1 3 none)
      obtain ⟨k, hk, rf, hl⟩ := ih zeroWord s'
        (readRegs (readRegs regs 1 3 (some bit)) 1 3 none) count hc seed.property.le
      have he := Eval.while_true
        (show (state (readRegs regs 1 3 (some bit)) {s with left := seed.val, zero := zeroWord.val, count := count}).regs 3 = true by
          simp [ readRegs_present])
        (hs.seq hp) hl
      refine ⟨m+1+k+1, ?_, rf, ?_⟩
      · nlinarith
      · simpa only [literalLoop, literalBits, literalEnd, literalLast,
          List.head?_cons, List.tail_cons, List.reverse_append, List.append_assoc, s'] using he

theorem literalScan_eval {B : ℕ} (n : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hnew : s.newTail.length ≤ B) :
    ∃ m ≤ n*(19*B+18)+2, ∃ rf, Eval literalScan m
      (state regs {s with left := seed.val, zero := zeroWord.val, count := count})
      (state rf {s with left := (literalEnd n seed zeroWord).val, zero := zeroWord.val, count := [], newTail := literalLast n seed zeroWord s.newTail, output := (literalBits n seed zeroWord).reverse ++ s.output}) := by
  have hp := popCount_eval {s with left := seed.val, zero := zeroWord.val, count := count} regs
  obtain ⟨m, hm, rf, hl⟩ := literalLoop_eval n seed zeroWord s regs count hcount hnew
  exact ⟨1+m, by omega, rf, hp.seq hl⟩

@[simp] theorem literalBits_length {B : ℕ} (n : ℕ) (seed zeroWord : Word B) :
    (literalBits n seed zeroWord).length = n*B := by
  induction n generalizing seed with
  | zero => simp [literalBits]
  | succ n ih =>
      simp only [literalBits, List.length_append, seed.property, ih]
      ring

theorem literalLast_length_le {B : ℕ} (n : ℕ) (seed zeroWord : Word B)
    (old : List Bool) (hold : old.length ≤ B) :
    (literalLast n seed zeroWord old).length ≤ B := by
  induction n generalizing seed old with
  | zero => exact hold
  | succ n ih => exact ih zeroWord seed.val seed.property.le


def literalWords {B : ℕ} : ℕ → Word B → Word B → List (Word B)
  | 0, _, _ => []
  | n+1, seed, zeroWord => seed :: literalWords n zeroWord zeroWord

@[simp] theorem literalWords_length {B : ℕ} (n : ℕ) (seed zeroWord : Word B) :
    (literalWords n seed zeroWord).length = n := by
  induction n generalizing seed with
  | zero => rfl
  | succ n ih => simpa [literalWords] using congrArg Nat.succ (ih zeroWord)

theorem literalWords_bits {B : ℕ} (n : ℕ) (seed zeroWord : Word B) :
    wordBits (literalWords n seed zeroWord) = literalBits n seed zeroWord := by
  induction n generalizing seed with
  | zero => rfl
  | succ n ih => simpa [wordBits, literalWords, literalBits] using congrArg (seed.val ++ ·) (ih zeroWord)

def literalLastWord {B : ℕ} : ℕ → Word B → Word B → Word B → Word B
  | 0, _, _, old => old
  | n+1, seed, zeroWord, _ => literalLastWord n zeroWord zeroWord seed

theorem literalLast_word {B : ℕ} (n : ℕ) (seed zeroWord old : Word B) :
    literalLast n seed zeroWord old.val = (literalLastWord n seed zeroWord old).val := by
  induction n generalizing seed old with
  | zero => rfl
  | succ n ih => exact ih zeroWord seed

theorem literalLast_independent {B : ℕ} (n : ℕ) (hn : 0 < n) (seed zeroWord : Word B)
    (x y : List Bool) : literalLast n seed zeroWord x = literalLast n seed zeroWord y := by
  cases n with
  | zero => omega
  | succ n => rfl

def initialData {B : ℕ} (d : ℕ) (oneWord zeroWord : Word B) : VectorData B d :=
  { coefficients := ⟨literalWords d oneWord zeroWord, literalWords_length d oneWord zeroWord⟩
    last := literalLastWord d oneWord zeroWord zeroWord }

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
