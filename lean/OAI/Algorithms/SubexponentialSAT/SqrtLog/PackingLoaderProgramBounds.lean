import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgramVerified

namespace OAI.Algorithms

/-! The loader's complete native cost, including emitted alphabet size. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def sizeBound (outside : Store) (scopes : List Bool) (n k f : ℕ) (pairs : List Bool) : ℕ :=
  extent (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs + scopes.length+n+k+f+
  SubexponentialSAT.BinaryArithmetic.toNat (outside 59)+SubexponentialSAT.BinaryArithmetic.toNat (outside 55)+
  (outside 55).length+(outside 56).length+(outside 57).length+(outside 58).length+
  (outside 59).length+1

private theorem unary_bound (bits : List Bool) (B : ℕ)
    (hv : SubexponentialSAT.BinaryArithmetic.toNat bits+1 ≤ B) (hl : bits.length+1 ≤ B) (_hB : 1 ≤ B) :
    LeafParametersProgram.Serialization.unaryCopyBound bits+1 ≤ 45*B^2 := by
  rw [LeafParametersProgram.Serialization.unaryCopyBound_eq]
  have hm : (SubexponentialSAT.BinaryArithmetic.toNat bits+1)*(bits.length+1) ≤ B^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hv hl
  have hsq : B ≤ B^2 := by nlinarith
  nlinarith

theorem budget_polynomial (outside : Store) (scopes : List Bool) (n k f : ℕ)
    (pairs : List Bool) (hr : 0 < SubexponentialSAT.BinaryArithmetic.toNat (outside 59)) :
    budget outside scopes n k f pairs ≤ 22000*(sizeBound outside scopes n k f pairs)^4 := by
  let B := sizeBound outside scopes n k f pairs
  have hB : 1 ≤ B := by dsimp [B,sizeBound]; omega
  have hE : extent (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
      (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs+1 ≤ B := by
    dsimp [B,sizeBound]; omega
  have hcore := (coreBudget_polynomial (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs hr).trans
      (Nat.mul_le_mul_left 21000 (Nat.pow_le_pow_left hE 4))
  have hR := unary_bound (outside 59) B
    (by dsimp [B,sizeBound]; omega) (by dsimp [B,sizeBound]; omega) hB
  have hQ := unary_bound (outside 55) B
    (by dsimp [B,sizeBound]; omega) (by dsimp [B,sizeBound]; omega) hB
  have hcapture : captureBudget scopes.length n k f ≤ 56*B := by
    dsimp [captureBudget,B,sizeBound]; omega
  have hfinish : finishBudget outside ≤ 60*B := by
    dsimp [finishBudget,B,sizeBound]; omega
  have hsq : B ≤ B^2 := by nlinarith
  have hpow : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have hone : 1 ≤ B^4 := hB.trans (hsq.trans hpow)
  change _ ≤ 22000*B^4
  unfold budget parameterBudget
  omega

/-- The instruction table is fixed, hence the final primitive simulation
adds only its constant compiler overhead. -/
theorem primitive_run (outside : Store) (regs : Fin 16 → Bool)
    (scopes : List Bool) (n k f : ℕ) (pairs : List Bool)
    (h60 : outside 60=[]) (hr : 0 < SubexponentialSAT.BinaryArithmetic.toNat (outside 59)) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (22000*(sizeBound outside scopes n k f pairs)^4))
      (primitiveCfg program ((rawInput outside regs scopes n k f pairs).withPC (some program.entry)))
      (primitiveCfg program ((framed (Function.update outside 60 scopes)
        (readyLocal rf (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
          (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs
          (outside 56) (outside 57) (outside 58) (outside 59))).withPC none)) := by
  obtain ⟨rf,h⟩ := program_run outside regs scopes n k f pairs h60 hr
  exact ⟨rf,(BitProgram.primitive_execution program h).mono
    (Nat.mul_le_mul_left _ (budget_polynomial outside scopes n k f pairs hr))⟩

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
