import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientCheckerHead

namespace OAI.Algorithms

/-! Actual A-step and R-step loops of the coefficient checker. Runtime
counters live on stacks; neither bound changes the finite instruction table. -/

namespace SubexponentialSAT.Subexp.CoefficientCheckerProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding
open CoefficientCheckerSemantics

variable (p : ℕ) [Fact p.Prime]

def popRegs (r : Fin 8 → Bool) (bits : List Bool) : Fin 8 → Bool :=
  Function.update r 0 (bits.head?.getD false)

theorem popA_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) :
    Eval popA 1 (ready p regs g neg ok xs a c)
      (ready p (popRegs regs a) a.head?.isSome neg ok xs a.tail c) := by
  have h : (StructuredProgram.Atom.pop 17 0 8).eval (ready p regs g neg ok xs a c) =
      ready p (popRegs regs a) a.head?.isSome neg ok xs a.tail c := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        readRegs, ready, wide, lowData, MatrixScalarProgram.state, popRegs]
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        ready, wide, lowData, MatrixScalarProgram.state]
  rw [← h]
  exact .base (.atom _ _)

theorem popChecks_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) :
    Eval popChecks 1 (ready p regs g neg ok xs a c)
      (ready p (popRegs regs c) c.head?.isSome neg ok xs a c.tail) := by
  have h : (StructuredProgram.Atom.pop 18 0 8).eval (ready p regs g neg ok xs a c) =
      ready p (popRegs regs c) c.head?.isSome neg ok xs a c.tail := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        readRegs, ready, wide, lowData, MatrixScalarProgram.state, popRegs]
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        ready, wide, lowData, MatrixScalarProgram.state]
  rw [← h]
  exact .base (.atom _ _)

theorem toggle_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a c : List Bool) :
    Eval toggle 1 (ready p regs g neg ok xs a c)
      (ready p regs g (!neg) ok xs a c) := by
  have h : (StructuredProgram.Atom.bnot 9 9).eval (ready p regs g neg ok xs a c) =
      ready p regs g (!neg) ok xs a c := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        ready, wide, lowData, MatrixScalarProgram.state]
    · rfl
  rw [← h]
  exact .base (.atom _ _)

/-- The advancing loop performs the number of shifts represented by its
actual unary input stack, while toggling the physical parity bit. -/
theorem advance_eval (A : ℕ) (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (c : List Bool) :
    ∃ n ≤ A * (shiftBudget xs.length (width p) + 3) + 2, ∃ regs',
      Eval advance n (ready p regs g neg ok xs (List.replicate A true) c)
        (ready p regs' false (advanceParity A neg) ok
          (CoefficientDynamics.shifts A xs) [] c) := by
  induction A generalizing regs g neg xs with
  | zero =>
      have hp := popA_eval p regs g neg ok xs [] c
      have hw : Eval (.while 8 (.seq shiftOnce (.seq toggle popA))) 1
          (ready p (popRegs regs []) false neg ok xs [] c)
          (ready p (popRegs regs []) false neg ok xs [] c) :=
        .while_false (by simp [ready, wide])
      exact ⟨2, by omega, popRegs regs [], hp.seq hw⟩
  | succ A ih =>
      let r₀ := popRegs regs (List.replicate (A + 1) true)
      have hp : Eval popA 1
          (ready p regs g neg ok xs (List.replicate (A + 1) true) c)
          (ready p r₀ true neg ok xs (List.replicate A true) c) := by
        simpa only [r₀, List.replicate_succ, List.head?_cons, Option.isSome_some, List.tail_cons]
          using popA_eval p regs g neg ok xs (List.replicate (A + 1) true) c
      obtain ⟨ns, hs, rs, es⟩ := shiftOnce_eval p r₀ true neg ok xs (List.replicate A true) c
      have et := toggle_eval p rs true neg ok (CoefficientDynamics.shift xs)
        (List.replicate A true) c
      obtain ⟨nr, hr, rr, er⟩ := ih rs true (!neg) (CoefficientDynamics.shift xs)
      simp only [CoefficientDynamics.shift_length] at hr
      change Eval (.seq popA (.while 8 (.seq shiftOnce (.seq toggle popA)))) nr _ _ at er
      cases er with
      | @seq _ _ nPop nWhile _ mid _ ePop eWhile =>
          have ew := Eval.while_true (test := (8 : Fin 11))
            (by simp [ready, wide]) (es.seq (et.seq ePop)) eWhile
          have ef := hp.seq ew
          refine ⟨1 + (ns + (1 + nPop) + nWhile + 1), ?_, rr, ?_⟩
          · simp only [Nat.succ_mul]
            omega
          · simpa only [advanceParity, CoefficientDynamics.shifts] using ef

/-- The part of the second loop after the saved dimension has been copied. -/
abbrev checkTail : Cmd 11 20 :=
  .seq popChecks (.while 8 (.seq compareHead (.seq shiftOnce (.seq toggle popChecks))))

def checkStepBudget (R B : ℕ) : ℕ := compareBudget R B + shiftBudget R B + 3

/-- Every comparison, shift, parity toggle, counter pop, and branch test is
included in the actual second-loop trace. -/
theorem checkTail_eval (R : ℕ) (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a : List Bool) (hR : R ≤ xs.length) :
    ∃ n ≤ R * checkStepBudget xs.length (width p) + 2, ∃ regs',
      Eval checkTail n (ready p regs g neg ok xs a (List.replicate R true))
        (ready p regs' false (advanceParity R neg) (ok && checkHeads R neg xs)
          (CoefficientDynamics.shifts R xs) a []) := by
  induction R generalizing regs g neg ok xs with
  | zero =>
      have hp := popChecks_eval p regs g neg ok xs a []
      have hw : Eval (.while 8 (.seq compareHead (.seq shiftOnce (.seq toggle popChecks)))) 1
          (ready p (popRegs regs []) false neg ok xs a [])
          (ready p (popRegs regs []) false neg ok xs a []) :=
        .while_false (by simp [ready, wide])
      refine ⟨2, by omega, popRegs regs [], ?_⟩
      simpa only [checkTail, List.replicate_zero, advanceParity,
        CoefficientDynamics.shifts, checkHeads, Bool.and_true]
        using hp.seq hw
  | succ R ih =>
      cases xs with
      | nil => simp at hR
      | cons x rest =>
          let r₀ := popRegs regs (List.replicate (R + 1) true)
          have hp : Eval popChecks 1
              (ready p regs g neg ok (x :: rest) a (List.replicate (R + 1) true))
              (ready p r₀ true neg ok (x :: rest) a (List.replicate R true)) := by
            simpa only [r₀, List.replicate_succ, List.head?_cons, Option.isSome_some,
              List.tail_cons]
              using popChecks_eval p regs g neg ok (x :: rest) a (List.replicate (R + 1) true)
          obtain ⟨nc, hc, rc, ec⟩ := compareHead_eval p r₀ true neg ok x rest a (List.replicate R true)
          let ok₁ := ok && decide (x = sign neg)
          obtain ⟨ns, hs, rs, es⟩ := shiftOnce_eval p rc true neg ok₁ (x :: rest) a
            (List.replicate R true)
          have et := toggle_eval p rs true neg ok₁ (CoefficientDynamics.shift (x :: rest))
            a (List.replicate R true)
          obtain ⟨nr, hr, rr, er⟩ := ih rs true (!neg) ok₁
            (CoefficientDynamics.shift (x :: rest)) (by simpa using Nat.le_of_succ_le hR)
          simp only [CoefficientDynamics.shift_length] at hr
          change Eval (.seq popChecks (.while 8
            (.seq compareHead (.seq shiftOnce (.seq toggle popChecks))))) nr _ _ at er
          cases er with
          | @seq _ _ nPop nWhile _ mid _ ePop eWhile =>
              have ew := Eval.while_true (test := (8 : Fin 11))
                (by simp [ready, wide]) (ec.seq (es.seq (et.seq ePop))) eWhile
              have ef := hp.seq ew
              refine ⟨1 + (nc + (ns + (1 + nPop)) + nWhile + 1), ?_, rr, ?_⟩
              · dsimp [checkStepBudget] at *
                simp only [Nat.succ_mul]
                omega
              · simpa only [advanceParity, CoefficientDynamics.shifts, checkHeads,
                  List.getD_cons_zero, Bool.and_assoc, ok₁] using ef

/-- Copying the saved dimension is also a physical operation. -/
theorem copyChecks_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a : List Bool) :
    Eval (copy 16 18) (7 * xs.length + 5) (ready p regs g neg ok xs a [])
      (ready p (readRegs regs 0 1 none) g neg ok xs a (List.replicate xs.length true)) := by
  let d := ready p regs g neg ok xs a []
  have he := SubexpScanPrimitives.copy_eval d 16 18 9 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [d, ready, wide, lowData, MatrixScalarProgram.state, MatrixScalarProgram.scalarStacks])
  have hf : afterCopy d 16 18 0 1 =
      ready p (readRegs regs 0 1 none) g neg ok xs a (List.replicate xs.length true) := by
    apply state_ext
    · funext j
      fin_cases j <;> simp [d, ready, wide, lowData, MatrixScalarProgram.state, afterCopy, readRegs]
    · funext j
      fin_cases j <;> simp [d, ready, wide, lowData, MatrixScalarProgram.state, afterCopy,
        MatrixScalarProgram.scalarStacks, StackRoutines.copyStacks]
  rw [hf] at he
  have hlen : (d.stacks 16).length = xs.length := by simp [d, ready, wide]
  simpa only [copy, hlen] using he

theorem checkConsecutive_eval (regs : Fin 8 → Bool) (g neg ok : Bool)
    (xs : List (ZMod p)) (a : List Bool) :
    ∃ n ≤ 7 * xs.length + 5 + (xs.length * checkStepBudget xs.length (width p) + 2),
      ∃ regs', Eval checkConsecutive n (ready p regs g neg ok xs a [])
        (ready p regs' false (advanceParity xs.length neg)
          (ok && checkHeads xs.length neg xs) (CoefficientDynamics.shifts xs.length xs) a []) := by
  have e₁ := copyChecks_eval p regs g neg ok xs a
  obtain ⟨n, hn, r, e₂⟩ := checkTail_eval p xs.length (readRegs regs 0 1 none) g neg ok xs a le_rfl
  exact ⟨7 * xs.length + 5 + n, Nat.add_le_add_left hn _, r, e₁.seq e₂⟩

end SubexponentialSAT.Subexp.CoefficientCheckerProgram

end OAI.Algorithms
