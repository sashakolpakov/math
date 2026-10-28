import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryArithmetic
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryExtract

namespace OAI.Algorithms

/-! Execution of the fixed joint-entry program on canonical type and scalar
bytes. All changing dimensions occur only in the runtime input stacks. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes

def positiveCost (base : Data) (p R Q A B : ℕ) : ℕ :=
  prepareCost base A B + coefficientStageCost p R Q B + finishEntryCost p A

theorem positive_eval (p : ℕ) [Fact p.Prime]
    (base : Data) (regs : Fin 9 → Bool) (xs : List (ZMod p)) (A B Q : ℕ)
    (hclear : ∀ j : Fin 37, j.val < 21 → base.stacks j = [])
    (hmod : base.stacks 29 = modulus p) (hzero : base.stacks 30 = word p 0)
    (hxs : base.stacks 31 = CoefficientPascalProgram.valueWords p xs)
    (hR : base.stacks 32 = List.replicate xs.length true)
    (hQ : base.stacks 22 = List.replicate Q true)
    (hA : A < xs.length + (Q + 1)) :
    ∃ n ≤ positiveCost base p xs.length Q A B, ∃ out,
      Eval positive n (counted base regs (A + 1) B)
        (finished base out p (MatrixPascalProgram.repeated p B (paddedCoefficients xs Q)) A B) := by
  obtain ⟨r1, t1⟩ := prepare_eval base regs A B hclear
  obtain ⟨n2, hn2, r2, t2⟩ := coefficientStage_eval p base r1 xs A B Q hmod hzero hxs hR hQ
  obtain ⟨n3, hn3, r3, t3⟩ := finishEntry_eval p base r2
    (MatrixPascalProgram.repeated p B (paddedCoefficients xs Q)) A B
    (by simpa [paddedCoefficients] using hA) hzero
  exact ⟨prepareCost base A B + (n2 + n3), by dsimp [positiveCost]; omega,
    r3, t1.seq (t2.seq t3)⟩

def zeroResult (base : Data) (regs : Fin 9 → Bool) (A B : ℕ) : Data :=
  copied (counted base regs A B) 30 0

theorem zero_eval (base : Data) (regs : Fin 9 → Bool) (A B : ℕ)
    (h9 : base.stacks 9 = []) :
    Eval (copy 30 0) (7 * (base.stacks 30).length + 5)
      (counted base regs A B) (zeroResult base regs A B) := by
  unfold zeroResult
  simpa [counted] using copy_eval (counted base regs A B) 30 0
    (by decide) (by decide) (by decide) (by simp [counted, h9])

theorem cleaned_zeroResult (base : Data) (regs out : Fin 9 → Bool) (A B : ℕ)
    (hclear : ∀ j : Fin 37, j.val < 21 → base.stacks j = [])
    (h33 : base.stacks 33 = []) (h34 : base.stacks 34 = [])
    (h35 : base.stacks 35 = []) (h36 : base.stacks 36 = []) :
    cleaned (zeroResult base regs A B) out = output base out (base.stacks 30) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp +decide [ zeroResult, copied, copyStacks, counted, cleanupPorts,
 hclear, h33, h34, h35, h36]

def programBudget {r Q Δ : ℕ} (p : ℕ) [Fact p.Prime] (i : Fin Δ)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) : ℕ :=
  let base := typedInput p i u y xs (fun _ => false)
  let A := MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows i u y)
  let B := MatrixScanProgram.transposedCount (MatrixEntryEvaluation.rows i u y)
  let ys := MatrixPascalProgram.repeated p B (paddedCoefficients xs Q)
  scanStageCost r Q Δ i.val +
    positiveCost base p xs.length Q (A - 1) B +
    cleanupCost (finished base (fun _ => false) p ys (A - 1) B) +
    (7 * (word p (0 : ZMod p)).length + 5) +
    cleanupCost (zeroResult base (fun _ => false) A B) + 2

variable {r Q Δ : ℕ}

/-- Canonical bytes for the actual normalized joint-matrix entry. The theorem
includes the terminal machine state and preserves all ten input stacks. -/
theorem program_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (u y : Joint t g i)
    (xs : List (ZMod p)) (regs : Fin 9 → Bool) :
    ∃ out, RunsIn program (programBudget p i u.val y.val xs)
      ((typedInput p i u.val y.val xs regs).withPC (some program.entry))
      ((output (typedInput p i u.val y.val xs regs) out
        (word p (ElementaryMatrix.jointMatrixDP i t g xs.length
          (fun j => xs.getD j 0 * (2 : ZMod p)^j) u y))).withPC none) := by
  let base := typedInput p i u.val y.val xs regs
  let rows := MatrixEntryEvaluation.rows i u.val y.val
  let A := MatrixScanProgram.unchangedCount rows
  let B := MatrixScanProgram.transposedCount rows
  let ys := MatrixPascalProgram.repeated p B (paddedCoefficients xs Q)
  have hclear : ∀ j : Fin 37, j.val < 21 → base.stacks j = [] := by
    intro j hj
    fin_cases j <;> simp +decide [base, typedInput, input] at *
  have h33 : base.stacks 33 = [] := by simp [base, typedInput, input]
  have h34 : base.stacks 34 = [] := by simp [base, typedInput, input]
  have h35 : base.stacks 35 = [] := by simp [base, typedInput, input]
  have h36 : base.stacks 36 = [] := by simp [base, typedInput, input]
  have hzero : base.stacks 30 = word p 0 := by simp [base, typedInput, input]
  obtain ⟨ns, hns, rs, ts, hrs⟩ := scanStage_eval p i u.val y.val xs regs
  have hvalue := MatrixEntryEvaluation.joint_entry_padded p h2 i t g xs (Q + 1) u y
  cases hc : decide (MatrixEntryKernel.SpectatorsAgree i u.val y.val) &&
      rows.all MatrixScanProgram.compatible with
  | false =>
      have hg : (counted base rs A B).regs 7 = false := by simpa [counted, rows, hc] using hrs
      have tz := zero_eval base rs A B (hclear 9 (by decide))
      obtain ⟨nc, hnc, rc, tc⟩ := cleanup_eval (zeroResult base rs A B)
        (by simpa [zeroResult, copied, copyStacks, counted] using hclear 9 (by decide))
        (by simp [zeroResult, copied, copyStacks, counted])
      rw [cleaned_zeroResult base rs rc A B hclear h33 h34 h35 h36, hzero] at tc
      have he := ts.seq ((Eval.ite_false (yes := positive) hg tz).seq tc)
      have hv : ElementaryMatrix.jointMatrixDP i t g xs.length
          (fun j => xs.getD j 0 * (2 : ZMod p)^j) u y = 0 := by
        simpa [rows, hc] using hvalue
      refine ⟨rc, ns + ((7 * (base.stacks 30).length + 5 + 1) + nc) + 1, ?_, ?_⟩
      · change ns + ((7 * (base.stacks 30).length + 5 + 1) + nc) + 1 ≤
          scanStageCost r Q Δ i.val +
            positiveCost base p xs.length Q (A - 1) B +
            cleanupCost (finished base (fun _ => false) p ys (A - 1) B) +
            (7 * (word p (0 : ZMod p)).length + 5) +
            cleanupCost (zeroResult base rs A B) + 2
        rw [hzero]
        omega
      · simpa only [program, command, base, hv] using compiled_halt_trace he 23 0
  | true =>
      have hg : (counted base rs A B).regs 7 = true := by simpa [counted, rows, hc] using hrs
      have hcompat : MatrixEntryKernel.AllCompatible i u.val y.val := by
        have hb := MatrixEntryEvaluation.compatibility_rows i u.val y.val
        rw [show (decide (MatrixEntryKernel.SpectatorsAgree i u.val y.val) &&
          (MatrixEntryEvaluation.rows i u.val y.val).all MatrixScanProgram.compatible) = true from hc] at hb
        exact of_decide_eq_true hb.symm
      have hApos : 0 < A := MatrixEntryEvaluation.unchangedCount_pos_joint i t g u y hcompat
      have hAle : A ≤ Q := MatrixEntryEvaluation.unchangedCount_le i u.val y.val
      obtain ⟨np, hnp, rp, tp⟩ := positive_eval p base rs xs (A - 1) B Q hclear
        (by simp [base, typedInput, input]) hzero
        (by simp [base, typedInput, input]) (by simp [base, typedInput, input])
        (by simp [base, typedInput, input]) (by omega)
      have hA : A - 1 + 1 = A := by omega
      rw [hA] at tp
      obtain ⟨nc, hnc, rc, tc⟩ := cleanup_eval (finished base rp p ys (A - 1) B)
        (by simp +decide [finished, coefficientResult, install, MatrixPascalProgram.resting,
          MatrixPascalProgram.stage, MatrixPascalProgram.frame, MatrixPascalProgram.extend,
 MatrixScalarProgram.scalarStacks])
        (by simp +decide [finished, coefficientResult, install, prepared])
      rw [cleaned_finished base rp rc p ys (A - 1) B hclear h33 h34 h35 h36] at tc
      have he := ts.seq ((Eval.ite_true (no := copy 30 0) hg tp).seq tc)
      have hv : ElementaryMatrix.jointMatrixDP i t g xs.length
          (fun j => xs.getD j 0 * (2 : ZMod p)^j) u y =
          (-1 : ZMod p)^(A - 1) * ys.getD (A - 1) 0 := by
        simpa [rows, A, B, ys, paddedCoefficients, hc] using hvalue
      refine ⟨rc, ns + ((np + 1) + nc) + 1, ?_, ?_⟩
      · change ns + ((np + 1) + nc) + 1 ≤
          scanStageCost r Q Δ i.val +
            positiveCost base p xs.length Q (A - 1) B +
            cleanupCost (finished base rp p ys (A - 1) B) +
            (7 * (word p (0 : ZMod p)).length + 5) +
            cleanupCost (zeroResult base rs A B) + 2
        omega
      · simpa only [program, command, base, hv] using compiled_halt_trace he 23 0

theorem primitive_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (u y : Joint t g i)
    (xs : List (ZMod p)) (regs : Fin 9 → Bool) :
    ∃ out, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * programBudget p i u.val y.val xs)
      (BitProgram.primitiveCfg program
        ((typedInput p i u.val y.val xs regs).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((output (typedInput p i u.val y.val xs regs) out
          (word p (ElementaryMatrix.jointMatrixDP i t g xs.length
            (fun j => xs.getD j 0 * (2 : ZMod p)^j) u y))).withPC none)) := by
  obtain ⟨out, ht⟩ := program_runsIn p h2 i t g u y xs regs
  exact ⟨out, BitProgram.primitive_execution _ ht⟩

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
