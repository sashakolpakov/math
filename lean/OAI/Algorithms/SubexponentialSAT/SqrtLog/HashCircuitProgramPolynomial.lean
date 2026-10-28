import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgramCostModel

namespace OAI.Algorithms

/-! A single fixed polynomial dominates the actual row-program envelope.
All numerical arguments are encoded dimensions, record counts, or retained-key
capacity; this theorem does not substitute field cardinality for bit width. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost
open MomentsProgram

theorem programBound_diagonal (Z : ℕ) :
    programBound Z Z Z Z Z Z Z Z =
      40000*Z^9+240220*Z^8+646660*Z^7+1019177*Z^6+1027670*Z^5+
      662234*Z^4+248322*Z^3+40637*Z^2+124*Z+7 := by
  unfold programBound rowBound payloadBound literalBound negativeBound bytesBound
    scaleBound normalizeBound productBound fetchBound Product.stepEnvelope Dictionary.codeBranchBudget
  ring

/-- A deliberately generous absolute degree-nine polynomial. -/
theorem programBound_le (B d n u J S k m Z : ℕ) (hZ : 1 ≤ Z)
    (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z) (hJ : J ≤ Z)
    (hS : S ≤ Z) (hk : k ≤ Z) (hm : m ≤ Z) :
    programBound B d n u J S k m ≤ 4000000*Z^9 := by
  have hmono : programBound B d n u J S k m ≤ programBound Z Z Z Z Z Z Z Z := by
    unfold programBound rowBound payloadBound literalBound negativeBound bytesBound
      scaleBound normalizeBound productBound fetchBound Product.stepEnvelope Dictionary.codeBranchBudget
    dsimp only
    gcongr
  have hpow (j : ℕ) (hj : j ≤ 9) : Z^j ≤ Z^9 := Nat.pow_le_pow_right hZ hj
  have h0 := hpow 0 (by decide)
  have h1 := hpow 1 (by decide)
  have h2 := hpow 2 (by decide)
  have h3 := hpow 3 (by decide)
  have h4 := hpow 4 (by decide)
  have h5 := hpow 5 (by decide)
  have h6 := hpow 6 (by decide)
  have h7 := hpow 7 (by decide)
  have h8 := hpow 8 (by decide)
  rw [programBound_diagonal] at hmono
  simp only [pow_zero,pow_one] at h0 h1
  omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost

end OAI.Algorithms
