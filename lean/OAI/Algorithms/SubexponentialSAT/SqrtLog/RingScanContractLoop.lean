import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanContract

namespace OAI.Algorithms

/-! Native whole-vector contraction, with both dimensions held on data tapes. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev blockBits {B : ℕ} : List (List (WordTriple B)) → List Bool
  | [] => []
  | b :: bs => tripleBits b ++ blockBits bs

abbrev contractBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (seed : Word (baseWidth p t)) : List (List (WordTriple (baseWidth p t))) → List Bool
  | [] => []
  | b :: bs => (foldTriples p t M seed b).val ++ contractBits p t M seed bs

abbrev contractPop : Cmd 8 20 := .base (.atom (.pop 15 1 3))
abbrev contractLoop : Cmd 8 20 := .while 3 (.seq contractStep contractPop)
abbrev contractScan : Cmd 8 20 := .seq contractPop contractLoop

private theorem update_outer (modulus left stream count width outer inner zero out next : List Bool) :
    Function.update (contractTapes modulus left stream count width outer inner zero out) 15 next =
    contractTapes modulus left stream count width next inner zero out := by
  funext i; by_cases h : i = 15
  · subst i; simp [contractTapes]
  · simp [contractTapes, h]

theorem contractPop_eval (regs : Fin 8 → Bool)
    (modulus left stream count width outer inner zero out : List Bool) :
    Eval contractPop 1 (contractState regs modulus left stream count width outer inner zero out)
      (contractState (readRegs regs 1 3 outer.head?) modulus left stream count width outer.tail inner zero out) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 20) 15 1 3)
    (contractState regs modulus left stream count width outer inner zero out) using 1
  cases outer <;> simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
    contractState, contractTapes, update_outer]

private theorem contractLoop_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner out : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 10 * baseWidth p t + 18) + 1,
      ∃ rf, Eval contractLoop n
      (contractState (readRegs regs 1 3 outer.head?) M.bits []
        (blockBits blocks ++ suffix) [] width outer.tail inner seed.val out)
      (contractState rf M.bits [] suffix [] width [] inner seed.val
        ((contractBits p t M seed blocks).reverse ++ out)) := by
  induction blocks generalizing regs outer out with
  | nil =>
      have he : outer = [] := List.length_eq_zero_iff.mp (by simpa using ho)
      subst outer
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      apply Eval.while_false
      simp [contractState, readRegs_present]
  | cons b bs ih =>
      cases outer with
      | nil => simp at ho
      | cons bit outer =>
          have ho' : outer.length = bs.length := by simpa using ho
          obtain ⟨n, hn, rf, hs⟩ := contractStep_eval p t M b seed (readRegs regs 1 3 (some bit))
            width (blockBits bs ++ suffix) outer inner out (hi b (by simp)) hw
          have hp := contractPop_eval rf M.bits [] (blockBits bs ++ suffix) [] width outer inner seed.val
            ((foldTriples p t M seed b).val.reverse ++ out)
          obtain ⟨m, hm, rg, hl⟩ := ih rf outer ((foldTriples p t M seed b).val.reverse ++ out)
            ho' (fun c hc => hi c (by simp [hc]))
          have he := Eval.while_true
            (show (contractState (readRegs regs 1 3 (some bit)) M.bits []
              (tripleBits b ++ (blockBits bs ++ suffix)) [] width outer inner seed.val out).regs 3 = true by
                simp [contractState, readRegs_present]) (hs.seq hp) hl
          refine ⟨n + 1 + m + 1, ?_, rg, ?_⟩
          · simp only [List.length_cons]; nlinarith
          · simpa only [contractLoop, blockBits, contractBits, List.head?_cons, List.tail_cons,
              List.reverse_append, List.append_assoc] using he

theorem contractScan_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner out : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 10 * baseWidth p t + 18) + 2,
      ∃ rf, Eval contractScan n
      (contractState regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val out)
      (contractState rf M.bits [] suffix [] width [] inner seed.val
        ((contractBits p t M seed blocks).reverse ++ out)) := by
  have hp := contractPop_eval regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val out
  obtain ⟨n, hn, rf, hl⟩ := contractLoop_eval p t M blocks seed regs width suffix outer inner out ho hi hw
  exact ⟨1+n, by omega, rf, hp.seq hl⟩

abbrev contractFinish : Cmd 8 20 := .call (transferProgram 18 0 1 3)
abbrev contractVector : Cmd 8 20 := .seq contractScan contractFinish

private theorem contract_finish_stacks (modulus stream width inner zero out : List Bool) :
    transferStacks (18 : Fin 20) 0 (contractTapes modulus [] stream [] width [] inner zero out) =
    contractTapes modulus out.reverse stream [] width [] inner zero [] := by
  funext i; fin_cases i <;> simp [transferStacks, contractTapes]

theorem contractFinish_eval (regs : Fin 8 → Bool) (modulus stream width inner zero out : List Bool) :
    Eval contractFinish (3 * out.length + 3)
      (contractState regs modulus [] stream [] width [] inner zero out)
      (contractState (readRegs regs 1 3 none) modulus out.reverse stream [] width [] inner zero []) := by
  have ht := transferProgram_trace (18 : Fin 20) 0 (1 : Fin 8) 3
    (by decide) (by decide) regs (contractTapes modulus [] stream [] width [] inner zero out)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [contractState, StructuredProgram.State.withPC, transferResult, contract_finish_stacks,
    show contractTapes modulus [] stream [] width [] inner zero out 18 = out from rfl,
    Nat.add_assoc] using hh

theorem contractBits_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (seed : Word (baseWidth p t)) (blocks : List (List (WordTriple (baseWidth p t)))) :
    (contractBits p t M seed blocks).length = blocks.length * baseWidth p t := by
  induction blocks with
  | nil => simp [contractBits]
  | cons b bs ih =>
      rw [contractBits, List.length_append, ih, List.length_cons, Nat.add_mul]
      simpa only [Nat.one_mul, Nat.add_comm] using
        congrArg (· + bs.length * baseWidth p t) (foldTriples p t M seed b).property

theorem contractVector_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ n ≤ blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 13 * baseWidth p t + 18) + 5,
      ∃ rf, Eval contractVector n
      (contractState regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val [])
      (contractState rf M.bits (contractBits p t M seed blocks) suffix [] width [] inner seed.val []) := by
  obtain ⟨n, hn, rf, hs⟩ := contractScan_eval p t M blocks seed regs width suffix outer inner [] ho hi hw
  simp only [List.append_nil] at hs
  have hf := contractFinish_eval rf M.bits suffix width inner seed.val (contractBits p t M seed blocks).reverse
  simp only [List.reverse_reverse, List.length_reverse, contractBits_length] at hf
  refine ⟨_, ?_, readRegs rf 1 3 none, hs.seq hf⟩
  nlinarith

abbrev contractVectorProgram : Program 8 20 (size contractVector + 1) := compiled contractVector 9 0

theorem contractVectorProgram_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t)
    (blocks : List (List (WordTriple (baseWidth p t)))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (width suffix outer inner : List Bool)
    (ho : outer.length = blocks.length)
    (hi : ∀ b ∈ blocks, inner.length = b.length) (hw : width.length = baseWidth p t) :
    ∃ rf, RunsIn contractVectorProgram
      (blocks.length * (inner.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 51)
        + 13 * baseWidth p t + 18) + 6)
      ((contractState regs M.bits [] (blockBits blocks ++ suffix) [] width outer inner seed.val []).withPC
        (some contractVectorProgram.entry))
      ((contractState rf M.bits (contractBits p t M seed blocks) suffix [] width [] inner seed.val []).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := contractVector_eval p t M blocks seed regs width suffix outer inner ho hi hw
  exact ⟨rf, n+1, by omega, compiled_halt_trace he 9 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
