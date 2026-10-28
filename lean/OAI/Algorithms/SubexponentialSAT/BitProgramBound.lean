import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile
import OAI.Algorithms.SubexponentialSAT.SubexpComputation

namespace OAI.Algorithms

/-! The uniform source-program contract for the revised theorem. A single
finite program is fixed before all input sizes, and its actual measured runs
are compiled by the proved compiler. This module does not supply the SAT
program or assume its existence. -/

namespace SubexponentialSAT.BitProgram

open SubexponentialSAT.SubexpComputation

/-- The source contract permits arbitrary terminal work data. All unbounded
parameters must be encoded on the stacks of the same fixed program `p`. -/
abbrev DecidesWithBound {r s l : ℕ} (p : Program r s l) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    ∃ (answer : Bool) (time : ℕ) (final : Cfg r s l),
      RunsIn p time (initial p (Encoding.encodeCNF F)) final ∧
      final.pc = none ∧
      (final.stacks p.outputStack).head? = some answer ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound constant exponentConstant degree
        (Encoding.formulaBitLength F) n

theorem primitive_decidesWithBound {r s l : ℕ} (p : Program r s l)
    {width degree : ℕ} {constant exponentConstant : ℝ}
    (h : DecidesWithBound p width constant exponentConstant degree) :
    SubexpComputation.DecidesWithBound (primitive p) width
      ((primitiveOverhead p : ℝ) * constant) exponentConstant degree := by
  intro n F hF
  obtain ⟨answer, time, final, run, halted, output, correct, bound⟩ := h n F hF
  refine ⟨answer, primitiveOverhead p * time,
    primitive_outputs_of_halted p run halted output, correct, ?_⟩
  rw [Nat.cast_mul, runtimeBound_mul_constant]
  exact mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg _)

/-- The final primitive target follows from one explicit uniform source
program and its measured run theorem; the compiler obligation is discharged. -/
theorem feasible_of_program {r s l : ℕ} (p : Program r s l)
    {width degree : ℕ} {constant exponentConstant : ℝ}
    (hc : 0 < constant) (ha : 0 < exponentConstant) (hd : 0 < degree)
    (h : DecidesWithBound p width constant exponentConstant degree) :
    SubexpComputation.Feasible width := by
  refine ⟨primitive p, (primitiveOverhead p : ℝ) * constant, exponentConstant, degree,
    mul_pos (Nat.cast_pos.mpr (primitiveOverhead_pos p)) hc, ha, hd, ?_⟩
  exact primitive_decidesWithBound p h

end SubexponentialSAT.BitProgram

end OAI.Algorithms
