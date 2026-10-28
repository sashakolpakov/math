import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramScore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectScores
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-! The physically normalized score is the unique fixed-width encoding of
the exact selector mass, independent of intermediate accumulator widths. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Score

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SubexpLiftRing

theorem canonical_score (regs : Fin 8 → Bool) (input width : List Bool)
    (z : ℕ) (hz : z < 2 ^ width.length) (hv : BinaryArithmetic.toNat input = z) :
    ∃ finalRegs, RunsIn program (14 * width.length + 2 * input.length + 15)
      ((data regs input [] width).withPC (some program.entry))
      ((data finalRegs (fixedBits width.length z) [] width).withPC none) := by
  obtain ⟨rf,word,hl,hv',he⟩ := exact_score regs input width (by simpa only [hv] using hz)
  have hw : word = fixedBits width.length z := by
    apply SubexpModulusConstruction.bits_eq_of_length_of_value
    · simpa using hl
    · rw [hv',hv,toNat_fixedBits_of_lt _ _ hz]
  exact ⟨rf,hw ▸ he⟩

theorem cnf_score {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (rows : List (HashSelect.Row m)) (regs : Fin 8 → Bool) (input width : List Bool)
    (hw : width.length = n + Nat.size m + 1)
    (hv : BinaryArithmetic.toNat input = HashSelect.mass (HashSelect.cnfRowAccept C)
      (HashInput.violationWeight C) rows) :
    ∃ finalRegs, RunsIn program (14 * width.length + 2 * input.length + 15)
      ((data regs input [] width).withPC (some program.entry))
      ((data finalRegs (fixedBits (n + Nat.size m + 1)
        (HashSelect.mass (HashSelect.cnfRowAccept C) (HashInput.violationWeight C) rows))
        [] width).withPC none) := by
  have hz : HashSelect.mass (HashSelect.cnfRowAccept C) (HashInput.violationWeight C) rows <
      2 ^ width.length := by rw [hw]; exact HashSelect.cnf_mass_lt_binary_capacity C rows
  simpa only [hw] using canonical_score regs input width _ hz hv

/-- Direct relocation preserves the entire caller outside these nine stacks
and eight registers, so payload, incumbent and candidate queue can be framed. -/
theorem canonical_score_lifted {R S : ℕ}
    (ρ : Fin 8 → Fin R) (σ : Fin 9 → Fin S)
    (hρ : Function.Injective ρ) (hσ : Function.Injective σ)
    (frame : State R S) (regs : Fin 8 → Bool) (input width : List Bool)
    (z : ℕ) (hz : z < 2 ^ width.length) (hv : BinaryArithmetic.toNat input = z) :
    ∃ steps finalRegs, steps ≤ 14 * width.length + 2 * input.length + 15 ∧
      Eval (.call (ProgramLinking.liftProgram program ρ σ)) steps
        (embedState ρ σ frame (data regs input [] width))
        (embedState ρ σ frame (data finalRegs (fixedBits width.length z) [] width)) := by
  obtain ⟨rf,k,hk,he⟩ := canonical_score regs input width z hz hv
  exact ⟨k,rf,hk,eval_call_lifted program ρ σ frame hρ hσ he⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Score

end OAI.Algorithms
