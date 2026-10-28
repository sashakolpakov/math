import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanTripleLoop

namespace OAI.Algorithms

/-! A fixed outer loop contracts a runtime-sized sequence of triple blocks. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def contractTapes (modulus left stream count width outer inner zero out : List Bool) :
    Fin 20 → List Bool := fun i =>
  if i = 0 then left else if i = 5 then modulus else if i = 9 then stream
  else if i = 11 then count else if i = 12 then width else if i = 15 then outer
  else if i = 16 then inner else if i = 17 then zero else if i = 18 then out else []

def contractState (regs : Fin 8 → Bool)
    (modulus left stream count width outer inner zero out : List Bool) : State 8 20 :=
  ⟨regs, contractTapes modulus left stream count width outer inner zero out⟩

def contractLower : Fin 15 → Fin 20 := Fin.castAdd 5

theorem contractLower_injective : Function.Injective contractLower := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 20 => x.val) h)

theorem embed_contract (regs oldRegs : Fin 8 → Bool)
    (modulus left oldLeft stream oldStream count oldCount width outer inner zero out : List Bool) :
    embedState id contractLower
      (contractState oldRegs modulus oldLeft oldStream oldCount width outer inner zero out)
      (addState regs modulus left [] [] stream [] count width) =
      contractState regs modulus left stream count width outer inner zero out := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id contractLower_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    simp [contractState, contractTapes, h0, h9, h11]

abbrev contractCoordinate : Cmd 8 20 := .call
  (ProgramLinking.liftProgram tripleScanProgram id contractLower)

theorem contractCoordinate_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix outer inner zero out : List Bool)
    (hc : count.length = triples.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 3,
      ∃ rf, Eval contractCoordinate n
      (contractState regs M.bits seed.val (tripleBits triples ++ suffix) count width outer inner zero out)
      (contractState rf M.bits (foldTriples p t M seed triples).val suffix [] width outer inner zero out) := by
  obtain ⟨rf, n, hn, ht⟩ := tripleScanProgram_run_suffix p t M triples seed regs count width suffix hc hw
  have he := eval_call_lifted tripleScanProgram id contractLower
    (contractState regs M.bits seed.val (tripleBits triples ++ suffix) count width outer inner zero out)
    Function.injective_id contractLower_injective ht
  exact ⟨n, hn, rf, by simpa only [embed_contract] using he⟩

abbrev contractCopyCount : Cmd 8 20 := .call (copyProgram 16 11 19 1 3)
abbrev contractCopyZero : Cmd 8 20 := .call (copyProgram 17 0 19 1 3)
abbrev contractEmit : Cmd 8 20 := .call (transferProgram 0 18 1 3)

private theorem copy_count_stacks (modulus stream width outer inner zero out : List Bool) :
    copyStacks (16 : Fin 20) 11
      (contractTapes modulus [] stream [] width outer inner zero out) =
    contractTapes modulus [] stream inner width outer inner zero out := by
  funext i; fin_cases i <;> simp [copyStacks, contractTapes]

private theorem copy_zero_stacks (modulus stream count width outer inner zero out : List Bool) :
    copyStacks (17 : Fin 20) 0
      (contractTapes modulus [] stream count width outer inner zero out) =
    contractTapes modulus zero stream count width outer inner zero out := by
  funext i; fin_cases i <;> simp [copyStacks, contractTapes]

private theorem contract_emit_stacks (modulus word stream width outer inner zero out : List Bool) :
    transferStacks (0 : Fin 20) 18
      (contractTapes modulus word stream [] width outer inner zero out) =
    contractTapes modulus [] stream [] width outer inner zero (word.reverse ++ out) := by
  funext i; fin_cases i <;> simp [transferStacks, contractTapes]

theorem contractCopyCount_eval (regs : Fin 8 → Bool)
    (modulus stream width outer inner zero out : List Bool) :
    Eval contractCopyCount (7 * inner.length + 5)
      (contractState regs modulus [] stream [] width outer inner zero out)
      (contractState (readRegs regs 1 3 none) modulus [] stream inner width outer inner zero out) := by
  have ht := copyProgram_trace (16 : Fin 20) 11 19 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide) regs
    (contractTapes modulus [] stream [] width outer inner zero out) (by rfl)
  have hh := halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, copyResult, copy_count_stacks,
    show contractTapes modulus [] stream [] width outer inner zero out 16 = inner from rfl,
    Nat.add_assoc] using hh

theorem contractCopyZero_eval (regs : Fin 8 → Bool)
    (modulus stream count width outer inner zero out : List Bool) :
    Eval contractCopyZero (7 * zero.length + 5)
      (contractState regs modulus [] stream count width outer inner zero out)
      (contractState (readRegs regs 1 3 none) modulus zero stream count width outer inner zero out) := by
  have ht := copyProgram_trace (17 : Fin 20) 0 19 (1 : Fin 8) 3
    (by decide) (by decide) (by decide) (by decide) regs
    (contractTapes modulus [] stream count width outer inner zero out) (by rfl)
  have hh := halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, copyResult, copy_zero_stacks,
    show contractTapes modulus [] stream count width outer inner zero out 17 = zero from rfl,
    Nat.add_assoc] using hh

theorem contractEmit_eval (regs : Fin 8 → Bool)
    (modulus word stream width outer inner zero out : List Bool) :
    Eval contractEmit (3 * word.length + 3)
      (contractState regs modulus word stream [] width outer inner zero out)
      (contractState (readRegs regs 1 3 none) modulus [] stream [] width outer inner zero
        (word.reverse ++ out)) := by
  have ht := transferProgram_trace (0 : Fin 20) 18 (1 : Fin 8) 3
    (by decide) (by decide) regs (contractTapes modulus word stream [] width outer inner zero out)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, transferResult, contract_emit_stacks,
    show contractTapes modulus word stream [] width outer inner zero out 0 = word from rfl,
    Nat.add_assoc] using hh

abbrev contractStep : Cmd 8 20 := .seq contractCopyCount
  (.seq contractCopyZero (.seq contractCoordinate contractEmit))

theorem contractStep_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner out : List Bool)
    (hc : inner.length = triples.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 10 * baseWidth p t + 16,
      ∃ rf, Eval contractStep n
      (contractState regs M.bits [] (tripleBits triples ++ suffix) [] width outer inner seed.val out)
      (contractState rf M.bits [] suffix [] width outer inner seed.val
        ((foldTriples p t M seed triples).val.reverse ++ out)) := by
  have h1 := contractCopyCount_eval regs M.bits (tripleBits triples ++ suffix) width outer inner seed.val out
  have h2 := contractCopyZero_eval (readRegs regs 1 3 none) M.bits
    (tripleBits triples ++ suffix) inner width outer inner seed.val out
  simp only [readRegs_reset] at h2
  obtain ⟨n, hn, rf, h3⟩ := contractCoordinate_eval p t M triples seed
    (readRegs regs 1 3 none) inner width suffix outer inner seed.val out hc hw
  have h4 := contractEmit_eval rf M.bits (foldTriples p t M seed triples).val suffix width outer inner seed.val out
  refine ⟨_, ?_, readRegs rf 1 3 none, h1.seq (h2.seq (h3.seq h4))⟩
  simp only [seed.property, (foldTriples p t M seed triples).property]
  rw [← hc] at hn
  nlinarith

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
