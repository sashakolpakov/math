import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularDivisionPrograms
import OAI.Algorithms.SubexponentialSAT.PositiveWordProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames
import OAI.Algorithms.SubexponentialSAT.SubexpDecodedCount

namespace OAI.Algorithms

/-!
# An actual finite program for the final count decision

The modulus and first coefficient are runtime Boolean words. The program
reduces the word modulo the modulus, then scans for a one bit. Both phases
execute inside one fixed 96-label instruction table.
-/

namespace SubexponentialSAT.SubexpDecodeProgram

open BitProgram ProgramLinking ModularDivisionPrograms
open PositiveWordProgram (positive residual)

def register : Fin 2 → Fin 8 := ![0, 1]
def port : Fin 1 → Fin 7 := fun _ => 0

theorem register_injective : Function.Injective register := by decide
theorem port_injective : Function.Injective port := by decide

abbrev scanProgram : Program 8 7 7 :=
  liftProgram PositiveWordProgram.program register port

def scanRegs (regs : Fin 8 → Bool) (value present : Bool) : Fin 8 → Bool :=
  Function.update (Function.update regs 0 value) 1 present

private theorem embed_scan (pc : Option (Fin 7)) (regs : Fin 8 → Bool)
    (v p : Bool) (word modulus : List Bool) :
    embedCfg register port id none
      (⟨none, regs, resting [] modulus []⟩ : Cfg 8 7 7)
      (PositiveWordProgram.cfg pc v p word) =
      ⟨pc, scanRegs regs v p, resting word modulus []⟩ := by
  apply embedCfg_eq_of_ports register port id none _ _ _
    register_injective port_injective
  · cases pc <;> rfl
  · intro i
    fin_cases i <;> simp [register, scanRegs, PositiveWordProgram.cfg,
      PositiveWordProgram.regs]
  · intro i hi
    have h0 : i ≠ 0 := fun he => hi ⟨0, by simpa [register] using he.symm⟩
    have h1 : i ≠ 1 := fun he => hi ⟨1, by simpa [register] using he.symm⟩
    simp [scanRegs, h0, h1]
  · intro i
    fin_cases i
    rfl
  · intro i hi
    have h0 : i ≠ 0 := fun he => hi ⟨0, by simpa [port] using he.symm⟩
    fin_cases i <;> simp_all [resting, seven]

@[simp] theorem scanRegs_self (regs : Fin 8 → Bool) :
    scanRegs regs (regs 0) (regs 1) = regs := by
  simp [scanRegs, Function.update_eq_self]

theorem scan_run (regs : Fin 8 → Bool) (word modulus : List Bool) :
    Trace scanProgram (PositiveWordProgram.cost word)
      ⟨some 0, regs, resting word modulus []⟩
      ⟨none, scanRegs regs (positive word) (positive word),
        resting (positive word :: residual word) modulus []⟩ := by
  have h := liftProgram_trace PositiveWordProgram.program register port
    (⟨none, regs, resting [] modulus []⟩ : Cfg 8 7 7)
    register_injective port_injective (PositiveWordProgram.run word (regs 0) (regs 1))
  simpa only [embed_scan, scanRegs_self] using h

abbrev program : Program 8 7 96 := link remainderProgram scanProgram

def answer (modulus input : List Bool) : Bool :=
  positive (ModularArithmetic.reduce modulus input)

/-- Actual execution from a prepared coefficient and modulus. Work stacks are
empty at entry. The result is the head of stack zero; the modulus is preserved. -/
theorem run (regs : Fin 8 → Bool) (modulus input : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn program (105 * (modulus.length + input.length + 1)^2)
        ⟨some 0, regs, resting [] modulus input⟩
        ⟨none, finalRegs,
          resting (answer modulus input :: residual (ModularArithmetic.reduce modulus input))
            modulus []⟩ := by
  obtain ⟨midRegs, hr⟩ := remainder_correct regs modulus input
  have hs := scan_run midRegs (ModularArithmetic.reduce modulus input) modulus
  have ht := link_runsIn remainderProgram scanProgram hr rfl
    (⟨_, le_rfl, hs⟩ : RunsIn scanProgram (PositiveWordProgram.cost
      (ModularArithmetic.reduce modulus input)) _ _)
  refine ⟨scanRegs midRegs (answer modulus input) (answer modulus input), ?_⟩
  apply ht.mono
  have hc := PositiveWordProgram.cost_le (ModularArithmetic.reduce modulus input)
  rw [ModularArithmetic.reduce_length] at hc
  nlinarith [sq_nonneg ((modulus.length + input.length : ℕ) : ℤ)]

theorem answer_iff (modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    answer modulus input = true ↔
      0 < BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus := by
  rw [answer, PositiveWordProgram.positive_iff,
    ModularArithmetic.reduce_correct _ _ hm]

/-- A primitive-tape trace of this same fixed program, with its compiler cost. -/
theorem primitive_run (regs : Fin 8 → Bool) (modulus input : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (105 * (modulus.length + input.length + 1)^2))
        (primitiveCfg program ⟨some 0, regs, resting [] modulus input⟩)
        (primitiveCfg program ⟨none, finalRegs,
          resting (answer modulus input :: residual (ModularArithmetic.reduce modulus input))
            modulus []⟩) := by
  obtain ⟨finalRegs, ht⟩ := run regs modulus input
  exact ⟨finalRegs, primitive_execution program ht⟩

/-- Quotient equality and the strict count bound identify the Boolean returned
by the finite program. In particular a noncanonical encoding of zero is reduced
before it is tested. -/
theorem count_answer_iff (p μ : ℕ) [Fact p.Prime] (hμ : 0 < μ)
    (c : Fin 4 → ZMod (p^μ))
    (a : SubexpQuarticRing.Quad (SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p μ)))
    (modulus : List Bool) (hmod : BinaryArithmetic.toNat modulus = p^μ)
    (count : ℕ) (hcount : count < p^μ)
    (hvalue : SubexpQuarticRing.quotientDenote c (a.map (SubexpQuarticRing.wordValue p μ)) =
      (count : LiftRing.Extension (QuarticSearch.poly c))) :
    answer modulus a.c0.val = true ↔ 0 < count := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hm : 0 < BinaryArithmetic.toNat modulus := by rw [hmod]; exact pow_pos hp μ
  rw [answer_iff _ _ hm, hmod, SubexpDecodedCount.first_mod_eq p μ hμ c a count hcount hvalue]

/-- The prepared coefficient representation gives a uniform quadratic bound
in its word width. This uses the actual binary modulus stored by setup. -/
theorem prepared_run (p μ : ℕ) (M : SubexpPreparedQuartic.Modulus p μ)
    (word : SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p μ))
    (regs : Fin 8 → Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn program (420 * (SubexpLiftRing.baseWidth p μ + 1)^2)
        ⟨some 0, regs, resting [] M.bits word.val⟩
        ⟨none, finalRegs,
          resting (answer M.bits word.val :: residual (ModularArithmetic.reduce M.bits word.val))
            M.bits []⟩ := by
  obtain ⟨finalRegs, ht⟩ := run regs M.bits word.val
  refine ⟨finalRegs, ht.mono ?_⟩
  have hlen : M.bits.length + word.val.length + 1 ≤
      2 * (SubexpLiftRing.baseWidth p μ + 1) := by
    have := M.length_le
    rw [word.property]
    omega
  calc
    105 * (M.bits.length + word.val.length + 1)^2 ≤
        105 * (2 * (SubexpLiftRing.baseWidth p μ + 1))^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen 2)
    _ = 420 * (SubexpLiftRing.baseWidth p μ + 1)^2 := by ring

end SubexponentialSAT.SubexpDecodeProgram

end OAI.Algorithms
