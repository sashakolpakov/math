import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableInitial

namespace OAI.Algorithms

/-! Physical dynamic-dimension constants. The same fixed loop emits a scalar
seed in coordinate zero followed by scalar zero in every other coordinate. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Constants

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing RingProgramTable

def input {B : ℕ} (s : Store) (seed zeroWord : Word B) : Store :=
  {s with left := seed.val, zero := zeroWord.val, count := [], newTail := [], output := [], vector := []}

def output {B : ℕ} (s : Store) (d : ℕ) (seed zeroWord : Word B) : Store :=
  {s with left := [], zero := zeroWord.val, count := [], newTail := [], output := [], vector := literalBits d seed zeroWord}

abbrev command : Cmd 8 27 :=
  .seq (copy 22 11) (.seq literalScan
    (.seq (transfer 20 15) (.seq (clear 0) (clear 19))))

def budget (B d : ℕ) : ℕ := d * (22 * B + 25) + 4 * B + 16

theorem command_eval {B : ℕ} (d : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (hd : s.degree.length = d) :
    ∃ n ≤ budget B d, ∃ finalRegs,
      Eval command n (state regs (input s seed zeroWord))
        (state finalRegs (output s d seed zeroWord)) := by
  let a := input s seed zeroWord
  let a1 := {a with count := s.degree}
  have hc := copy_store_eval a a1 regs 22 11 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, a1, a, input])
  obtain ⟨n,hn,rf,he⟩ := literalScan_eval d seed zeroWord a
    (readRegs regs 1 3 none) s.degree hd (by simp [a,input])
  let b := {a with left := (literalEnd d seed zeroWord).val, count := [], newTail := literalLast d seed zeroWord [], output := (literalBits d seed zeroWord).reverse}
  have he' : Eval literalScan n (state (readRegs regs 1 3 none) a1) (state rf b) := by
    simpa [a1,b,a,input] using he
  let c := {b with output := [], vector := literalBits d seed zeroWord}
  let e := {c with left := []}
  let f := {e with newTail := []}
  have ht := transfer_store_eval b c rf 20 15 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks,tapes,b,c,a,input])
  have hl := clear_store_eval c e (readRegs rf 1 3 none) 0 (by
    funext i; fin_cases i <;> simp [clearStacks,tapes,e])
  have hnew := clear_store_eval e f (readRegs rf 1 3 none) 19 (by
    funext i; fin_cases i <;> simp [clearStacks,tapes,f])
  simp only [readRegs_reset] at hl hnew
  have hlast : (literalLast d seed zeroWord []).length ≤ B :=
    literalLast_length_le d seed zeroWord [] (by simp)
  refine ⟨7*(tapes a 22).length+5 + (n + (3*(tapes b 20).length+3 +
    (2*(tapes c 0).length+3 + (2*(tapes e 19).length+3)))),?_,readRegs rf 1 3 none,?_⟩
  · change 7*s.degree.length+5 + (n + (3*(literalBits d seed zeroWord).reverse.length+3 +
      (2*(literalEnd d seed zeroWord).val.length+3 +
        (2*(literalLast d seed zeroWord []).length+3)))) ≤ budget B d
    have hend : (literalEnd d seed zeroWord).val.length = B := (literalEnd d seed zeroWord).property
    rw [hd,List.length_reverse,literalBits_length,hend]
    unfold budget
    nlinarith
  · simpa only [command,a,a1,b,c,e,f,input,output] using hc.seq (he'.seq (ht.seq (hl.seq hnew)))

def program := compiled command 0 15

theorem program_run {B : ℕ} (d : ℕ) (seed zeroWord : Word B)
    (s : Store) (regs : Fin 8 → Bool) (hd : s.degree.length = d) :
    ∃ finalRegs, RunsIn program (budget B d + 1)
      ((state regs (input s seed zeroWord)).withPC (some program.entry))
      ((state finalRegs (output s d seed zeroWord)).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval d seed zeroWord s regs hd
  exact ⟨rf,n+1,Nat.add_le_add_right hn 1,compiled_halt_trace he 0 15⟩

theorem zero_bits {B : ℕ} (d : ℕ) (zeroWord : Word B)
    (hz : zeroWord.val = List.replicate B false) :
    literalBits d zeroWord zeroWord = List.replicate (d * B) false := by
  induction d with
  | zero => simp only [literalBits, Nat.zero_mul, List.replicate_zero]
  | succ d ih =>
      rw [literalBits, ih, hz, Nat.succ_mul, Nat.add_comm (d * B) B, List.replicate_add]

end SubexponentialSAT.SqrtLog.LeafProgram.Constants

end OAI.Algorithms
