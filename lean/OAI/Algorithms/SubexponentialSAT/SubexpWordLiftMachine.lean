import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWordLift
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms

namespace OAI.Algorithms

/-!
# A fixed program for lifting one encoded residue coefficient

The input residue word is on stack 6, the stored source modulus on stack 5,
and a runtime target-width shape on stack 7. The program reduces the input,
normalizes to the supplied width, returns the exact `liftWordRun` output on
stack 0, and preserves the modulus. All work and shape stacks are cleared.
-/

namespace SubexponentialSAT.SubexpWordLiftMachine

open BitProgram ProgramLinking BinaryArithmetic
open SubexpLiftRing SubexpQuarticRing
open ModularDivisionPrograms ModularRingPrograms

abbrev program : Program 8 8 101 :=
  link (liftProgram remainderProgram id sevenPorts) normalizeProgram

private theorem embedded_seven {l : ℕ} (pc : Option (Fin l))
    (regs frameRegs : Fin 8 → Bool) (base frameBase : Fin 7 → List Bool)
    (shape : List Bool) :
    embedCfg id sevenPorts id none
      (⟨none, frameRegs, extendSeven frameBase shape⟩ : Cfg 8 8 l)
      ⟨pc, regs, base⟩ = ⟨pc, regs, extendSeven base shape⟩ := by
  apply ModularRingPrograms.embed_ports sevenPorts sevenPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0,rfl⟩)
    · exact False.elim (hi ⟨1,rfl⟩)
    · exact False.elim (hi ⟨2,rfl⟩)
    · exact False.elim (hi ⟨3,rfl⟩)
    · exact False.elim (hi ⟨4,rfl⟩)
    · exact False.elim (hi ⟨5,rfl⟩)
    · exact False.elim (hi ⟨6,rfl⟩)
    · rfl

def runtimeBound (inputWidth targetWidth modulusWidth : ℕ) : ℕ :=
  100 * (modulusWidth + inputWidth + 1)^2 +
    7 * targetWidth + 2 * (modulusWidth + inputWidth) + 9

theorem runtimeBound_uniform (b B m : ℕ) (hm : m ≤ b + 1) :
    runtimeBound b B m ≤ 500 * (b + B + 2)^2 := by
  have hsum : m + b + 1 ≤ 2 * (b + B + 2) := by omega
  have hquad : 100 * (m + b + 1)^2 ≤ 400 * (b + B + 2)^2 := by
    calc
      _ ≤ 100 * (2 * (b + B + 2))^2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2)
      _ = _ := by ring
  have hsq : b + B + 2 ≤ (b + B + 2)^2 := by
    simpa only [pow_two, Nat.mul_one] using
      Nat.mul_le_mul_left (b + B + 2) (show 1 ≤ b + B + 2 by omega)
  unfold runtimeBound
  omega

variable (p μ : ℕ) [Fact p.Prime]

theorem run (M : SubexpPreparedQuartic.Modulus p 1) (hμ : 0 < μ)
    (regs : Fin 8 → Bool) (x : Word (baseWidth p 1)) (shape : List Bool)
    (hshape : shape.length = baseWidth p μ) :
    ∃ finalRegs, RunsIn program
      (runtimeBound (baseWidth p 1) (baseWidth p μ) M.bits.length)
      ⟨some program.entry, regs, extendSeven (resting [] M.bits x.val) shape⟩
      ⟨none, finalRegs,
        extendSeven (resting (SubexpWordLift.liftWordRun p μ M x).1.val M.bits []) []⟩ := by
  have hm : BinaryArithmetic.toNat M.bits = p := by simpa only [pow_one] using M.value
  have hmpos : 0 < BinaryArithmetic.toNat M.bits := by rw [hm]; exact (Fact.out : p.Prime).pos
  obtain ⟨r₁, output, hr, hlen, hvalue⟩ := remainder_value regs M.bits x.val hmpos
  have lifted := liftProgram_runsIn remainderProgram id sevenPorts
    (⟨none, regs, extendSeven (resting [] M.bits []) shape⟩ : Cfg 8 8 89)
    Function.injective_id sevenPorts_injective hr
  rw [embedded_seven, embedded_seven] at lifted
  obtain ⟨r₂, hn⟩ := normalize_correct r₁ output shape M.bits
  have hvalueBound : BinaryArithmetic.toNat output < 2^shape.length := by
    rw [hvalue, hm, hshape]
    exact (Nat.mod_lt _ (Fact.out : p.Prime).pos).trans_le
      ((Nat.le_pow hμ).trans (modulus_le_width p μ))
  have heq : ModularArithmetic.padTo shape output =
      (SubexpWordLift.liftWordRun p μ M x).1.val := by
    apply SubexpModulusConstruction.bits_eq_of_length_of_value
    · simpa only [ModularArithmetic.padTo_length, hshape] using
        (SubexpWordLift.liftWordRun p μ M x).1.property.symm
    · rw [padTo_value_of_lt shape output hvalueBound, hvalue, hm,
        SubexpWordLift.liftWordRun_raw p μ M hμ x]
      simp only [SubexpWordLift.sourceValue, ZMod.val_natCast]
  have total := link_runsIn (liftProgram remainderProgram id sevenPorts) normalizeProgram
    lifted rfl hn
  refine ⟨r₂, ?_⟩
  simpa [program, runtimeBound, hlen, x.property, hshape, heq,
    normalizationState, extendSeven, resting, seven, relabelCfg, relocatePc,
    Nat.add_assoc] using total

/-- The actual fixed program lowers to primitive Boolean-stack execution. -/
theorem primitive_run (M : SubexpPreparedQuartic.Modulus p 1) (hμ : 0 < μ)
    (regs : Fin 8 → Bool) (x : Word (baseWidth p 1)) (shape : List Bool)
    (hshape : shape.length = baseWidth p μ) :
    ∃ finalRegs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        runtimeBound (baseWidth p 1) (baseWidth p μ) M.bits.length)
      (primitiveCfg program
        ⟨some program.entry, regs, extendSeven (resting [] M.bits x.val) shape⟩)
      (primitiveCfg program
        ⟨none, finalRegs,
          extendSeven (resting (SubexpWordLift.liftWordRun p μ M x).1.val M.bits []) []⟩) := by
  obtain ⟨rf, hr⟩ := run p μ M hμ regs x shape hshape
  exact ⟨rf, primitive_execution _ hr⟩

end SubexponentialSAT.SubexpWordLiftMachine

end OAI.Algorithms
