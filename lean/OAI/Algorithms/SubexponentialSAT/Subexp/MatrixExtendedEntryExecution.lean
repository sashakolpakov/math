import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryExecution

namespace OAI.Algorithms

/-! Terminal execution of the actual zero-extended entry service. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open BitProgram StructuredCalls StackRoutines MatrixWordEncoding MulticolorTypes

variable {r Q Δ : ℕ}

def value (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) : ZMod p :=
  SubexpAnnihilation.zeroExtendMatrix (joint t (y.head t) i)
    (ElementaryMatrix.jointMatrixDP i t (y.head t) xs.length
      (fun j => xs.getD j 0 * (2 : ZMod p)^j)) u y

def programBudget (p : ℕ) [Fact p.Prime] (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (xs : List (ZMod p)) : ℕ :=
  guardStageCost r Q Δ i.val t.val + MatrixEntryProgram.programBudget p i u y xs +
    7 * width p + 7

/-- Every type and field parameter is runtime data. The result is the
canonical scalar word and every input stack, including the cursor, is restored. -/
theorem program_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
    (regs : Fin 10 → Bool) :
    ∃ out, RunsIn program (programBudget p i t u y xs)
      ((typedInput p i t u y xs regs).withPC (some program.entry))
      ((output (typedInput p i t u y xs regs) out (word p (value p i t u y xs))).withPC none) := by
  let base := typedInput p i t u y xs regs
  obtain ⟨ng, hng, b, tg, hbs, hbr⟩ := guardStage_eval p i t u y xs regs
  by_cases hv : anchorValid i t u y
  · let uj : Joint t (y.head t) i := ⟨u, hv.1, hv.2.1⟩
    let yj : Joint t (y.head t) i := ⟨y, rfl, hv.2.2⟩
    let lr : Fin 9 → Bool := fun j => b.regs (j.castLE (by decide : 9 ≤ 10))
    have hin : project (by decide : 9 ≤ 10) (by decide : 37 ≤ 42) b =
        MatrixEntryProgram.typedInput p i u y xs lr := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        simp only [ hbs]
        simp [typedInput, j.isLt]
        rfl
    obtain ⟨rr, nj, hnj, tj⟩ := MatrixEntryProgram.program_runsIn p h2 i t (y.head t) uj yj xs lr
    change Trace MatrixEntryProgram.program nj
      ((MatrixEntryProgram.typedInput p i u y xs lr).withPC (some MatrixEntryProgram.program.entry))
      ((MatrixEntryProgram.output (MatrixEntryProgram.typedInput p i u y xs lr) rr
        (word p (ElementaryMatrix.jointMatrixDP i t (y.head t) xs.length
          (fun j => xs.getD j 0 * (2 : ZMod p)^j) uj yj))).withPC none) at tj
    let localOut := MatrixEntryProgram.output (MatrixEntryProgram.typedInput p i u y xs lr) rr
      (word p (ElementaryMatrix.jointMatrixDP i t (y.head t) xs.length
        (fun j => xs.getD j 0 * (2 : ZMod p)^j) uj yj))
    have tj' : Trace MatrixEntryProgram.program nj
        ((project (by decide : 9 ≤ 10) (by decide : 37 ≤ 42) b).withPC
          (some MatrixEntryProgram.program.entry)) (localOut.withPC none) := by
      simpa only [hin] using tj
    have te := liftCall_eval MatrixEntryProgram.program (by decide) (by decide) b localOut tj'
    let c := install b localOut
    have hvalue : value p i t u y xs =
        ElementaryMatrix.jointMatrixDP i t (y.head t) xs.length
          (fun j => xs.getD j 0 * (2 : ZMod p)^j) uj yj :=
      zeroExtend_of_valid i t u y _ hv
    have hout : c = output base c.regs (word p (value p i t u y xs)) := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        simp only [ localOut, MatrixEntryProgram.output]
        rw [hvalue]
        fin_cases j <;>
          simp +decide [hbs, base, typedInput, MatrixEntryProgram.typedInput, MatrixEntryProgram.input]
    change install b localOut = output base c.regs (word p (value p i t u y xs)) at hout
    rw [hout] at te
    have hguard : b.regs 9 = true := by simpa [hv] using hbr
    have he := tg.seq (Eval.ite_true (no := copyZero) hguard te)
    refine ⟨c.regs, ng + (nj + 1) + 1, ?_, ?_⟩
    · dsimp [programBudget]
      change nj ≤ MatrixEntryProgram.programBudget p i u y xs at hnj
      omega
    · simpa only [program, command, base] using compiled_halt_trace he 23 0
  · have hguard : b.regs 9 = false := by simpa [hv] using hbr
    have h0 : b.stacks 0 = [] := by
      rw [hbs]
      simp +decide [typedInput, MatrixEntryProgram.typedInput, MatrixEntryProgram.input]
    have h8 : b.stacks 8 = [] := by
      rw [hbs]
      simp +decide [typedInput, MatrixEntryProgram.typedInput, MatrixEntryProgram.input]
    have h30 : b.stacks 30 = word p 0 := by
      rw [hbs]
      simp +decide [typedInput, MatrixEntryProgram.typedInput, MatrixEntryProgram.input]
    have tz := TupleProgram.copy_eval (30 : Fin 42) 0 8 (0 : Fin 10) 1
      (by decide) (by decide) (by decide) (by decide) b h8
    let c : Data := ⟨readRegs b.regs 0 1 none, copyStacks 30 0 b.stacks⟩
    have hout : c = output base c.regs (word p 0) := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j
        by_cases hj : j = 0
        · subst j; simp [ copyStacks, h30, h0]
        · simp [ copyStacks, hj, hbs, base]
    change Eval copyZero (7 * (b.stacks 30).length + 5) b c at tz
    rw [hout] at tz
    have hvalue : value p i t u y xs = 0 := zeroExtend_of_invalid i t u y _ hv
    have he := tg.seq (Eval.ite_false
      (yes := liftCall MatrixEntryProgram.program (by decide) (by decide)) hguard tz)
    refine ⟨c.regs, ng + (7 * (b.stacks 30).length + 5 + 1) + 1, ?_, ?_⟩
    · rw [h30, word_length]
      dsimp [programBudget]
      omega
    · simpa only [program, command, base, hvalue] using compiled_halt_trace he 23 0

theorem primitive_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
    (regs : Fin 10 → Bool) :
    ∃ out, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * programBudget p i t u y xs)
      (BitProgram.primitiveCfg program
        ((typedInput p i t u y xs regs).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((output (typedInput p i t u y xs regs) out (word p (value p i t u y xs))).withPC none)) := by
  obtain ⟨out, ht⟩ := program_runsIn p h2 i t u y xs regs
  exact ⟨out, BitProgram.primitive_execution _ ht⟩

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
