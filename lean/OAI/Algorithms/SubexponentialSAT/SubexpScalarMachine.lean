import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms

namespace OAI.Algorithms

/-!
# Exact machine refinement of the prepared scalar callbacks

The program output agrees as a Boolean list with the callback output, not
only modulo the coefficient modulus. Fixed width and binary-value uniqueness
give the final identification. The program tables are independent of p and mu.
-/

namespace SubexponentialSAT.SubexpScalarMachine

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

private theorem modulus_pos : 0 < BinaryArithmetic.toNat M.bits := by
  rw [M.value]
  exact pow_pos (Fact.out : p.Prime).pos μ

omit [Fact (Nat.Prime p)] in
private theorem modulus_capacity : BinaryArithmetic.toNat M.bits ≤ 2^baseWidth p μ := by
  rw [M.value]
  exact modulus_le_width p μ

theorem wordAdd_run (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ)) :
    ∃ finalRegs,
      RunsIn wordAddProgram (6000 * (baseWidth p μ + 1)^2)
        ⟨some wordAddProgram.entry, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩
        ⟨none, finalRegs,
          extendSeven (resting (SubexpPreparedQuartic.wordAdd p μ M x y).1.val M.bits []) []⟩ := by
  obtain ⟨rf, output, hr, hlen, hv⟩ := wordAdd_value regs x.val y.val M.bits
    (baseWidth p μ) x.property y.property M.length_le
    (modulus_pos p μ M) (modulus_capacity p μ M)
  have hvalue : BinaryArithmetic.toNat (SubexpPreparedQuartic.wordAdd p μ M x y).1.val =
      (BinaryArithmetic.toNat x.val + BinaryArithmetic.toNat y.val) % BinaryArithmetic.toNat M.bits :=
    addBaseRun_value _ _ _ _ (modulus_pos p μ M) (modulus_capacity p μ M)
  have heq : output = (SubexpPreparedQuartic.wordAdd p μ M x y).1.val :=
    SubexpModulusConstruction.bits_eq_of_length_of_value _ _
      (hlen.trans (SubexpPreparedQuartic.wordAdd p μ M x y).1.property.symm)
      (hv.trans hvalue.symm)
  exact ⟨rf, heq ▸ hr⟩

theorem wordMul_run (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ)) :
    ∃ finalRegs,
      RunsIn wordMulProgram (6000 * (baseWidth p μ + 1)^2)
        ⟨some wordMulProgram.entry, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩
        ⟨none, finalRegs,
          extendSeven (resting (SubexpPreparedQuartic.wordMul p μ M x y).1.val M.bits []) []⟩ := by
  obtain ⟨rf, output, hr, hlen, hv⟩ := wordMul_value regs x.val y.val M.bits
    (baseWidth p μ) x.property y.property M.length_le
    (modulus_pos p μ M) (modulus_capacity p μ M)
  have hvalue : BinaryArithmetic.toNat (SubexpPreparedQuartic.wordMul p μ M x y).1.val =
      (BinaryArithmetic.toNat x.val * BinaryArithmetic.toNat y.val) % BinaryArithmetic.toNat M.bits :=
    mulBaseRun_value _ _ _ _ (modulus_pos p μ M) (modulus_capacity p μ M)
  have heq : output = (SubexpPreparedQuartic.wordMul p μ M x y).1.val :=
    SubexpModulusConstruction.bits_eq_of_length_of_value _ _
      (hlen.trans (SubexpPreparedQuartic.wordMul p μ M x y).1.property.symm)
      (hv.trans hvalue.symm)
  exact ⟨rf, heq ▸ hr⟩

/-- The fixed add program is compiled into actual primitive machine steps. -/
theorem wordAdd_primitive (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ)) :
    ∃ finalRegs,
      SubexponentialSAT.Computation.RunsIn (primitive wordAddProgram).step
        (primitiveOverhead wordAddProgram * (6000 * (baseWidth p μ + 1)^2))
        (primitiveCfg wordAddProgram
          ⟨some wordAddProgram.entry, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩)
        (primitiveCfg wordAddProgram
          ⟨none, finalRegs,
            extendSeven (resting (SubexpPreparedQuartic.wordAdd p μ M x y).1.val M.bits []) []⟩) := by
  obtain ⟨rf, hr⟩ := wordAdd_run p μ M regs x y
  exact ⟨rf, primitive_execution _ hr⟩

/-- The fixed multiply program is compiled into actual primitive machine steps. -/
theorem wordMul_primitive (regs : Fin 8 → Bool) (x y : Word (baseWidth p μ)) :
    ∃ finalRegs,
      SubexponentialSAT.Computation.RunsIn (primitive wordMulProgram).step
        (primitiveOverhead wordMulProgram * (6000 * (baseWidth p μ + 1)^2))
        (primitiveCfg wordMulProgram
          ⟨some wordMulProgram.entry, regs, extendSeven (scalarInput x.val y.val M.bits) []⟩)
        (primitiveCfg wordMulProgram
          ⟨none, finalRegs,
            extendSeven (resting (SubexpPreparedQuartic.wordMul p μ M x y).1.val M.bits []) []⟩) := by
  obtain ⟨rf, hr⟩ := wordMul_run p μ M regs x y
  exact ⟨rf, primitive_execution _ hr⟩

end SubexponentialSAT.SubexpScalarMachine

end OAI.Algorithms
