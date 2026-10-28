import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBoundsServices
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgramLoopFinal

namespace OAI.Algorithms

/-! Uniform numerical bounds. Z bounds encoded sizes and retained capacity,
not merely the bit length of the original formula. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open HashCircuitProgram

theorem hashServiceBound_mono (B d n u J N k m L Z : ℕ)
    (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z) (hJ : J ≤ Z)
    (hN : N ≤ Z) (hk : k ≤ Z) (hm : m ≤ Z) (hL : L ≤ Z) :
    hashServiceBound B d n u J N k m L ≤ hashServiceBound Z Z Z Z Z Z Z Z Z := by
  dsimp only [hashServiceBound,tableBound,Cost.programBound,Cost.rowBound,Cost.payloadBound,
    Cost.literalBound,Cost.negativeBound,Cost.fetchBound,Cost.bytesBound,Cost.productBound,
    Cost.scaleBound,Cost.normalizeBound,
    IdempotentApplyProgram.Bounds.totalEnvelope,IdempotentApplyProgram.Bounds.prepareEnvelope,
    IdempotentApplyProgram.Bounds.arithmeticEnvelope,IdempotentApplyProgram.Bounds.complementEnvelope,
    IdempotentApplyProgram.Bounds.scaleStepEnvelope,IdempotentApplyProgram.Bounds.normalizeStepEnvelope,
    IdempotentApplyProgram.Bounds.applyEnvelope,IdempotentApplyProgram.Bounds.loopEnvelope,
    IdempotentApplyProgram.Bounds.quadraticEnvelope,IdempotentApplyProgram.Bounds.accumulatorEnvelope,
    IdempotentApplyProgram.Bounds.wordEnvelope,IdempotentApplyProgram.Bounds.mulEnvelope,
    IdempotentApplyProgram.Bounds.addEnvelope,IdempotentApplyProgram.Bounds.byteCapacity,
    MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
  gcongr

theorem hashServiceBound_diagonal (Z : ℕ) :
    hashServiceBound Z Z Z Z Z Z Z Z Z =
      40000*Z^9+360220*Z^8+1367320*Z^7+2879817*Z^6+3704995*Z^5+
      2976138*Z^4+1442724*Z^3+380529*Z^2+42371*Z+376 := by
  unfold hashServiceBound
  rw [IdempotentApplyProgram.Bounds.totalEnvelope_diagonal]
  dsimp only [tableBound,Cost.programBound,Cost.rowBound,Cost.payloadBound,
    Cost.literalBound,Cost.negativeBound,Cost.fetchBound,Cost.bytesBound,Cost.productBound,
    Cost.scaleBound,Cost.normalizeBound,
    MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
  ring

theorem hashServiceBound_le (B d n u J N k m L Z : ℕ) (hZ : 1 ≤ Z)
    (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z) (hJ : J ≤ Z)
    (hN : N ≤ Z) (hk : k ≤ Z) (hm : m ≤ Z) (hL : L ≤ Z) :
    hashServiceBound B d n u J N k m L ≤ 14000000*Z^9 := by
  apply (hashServiceBound_mono B d n u J N k m L Z hB hd hn hu hJ hN hk hm hL).trans
  rw [hashServiceBound_diagonal]
  have hp (k : ℕ) (hk : k ≤ 9) : Z^k ≤ Z^9 := Nat.pow_le_pow_right hZ hk
  have h0 : 1 ≤ Z^9 := by simpa using hp 0 (by decide)
  have h1 : Z ≤ Z^9 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  omega

theorem markedServiceBound_le (B d n u J N k Z : ℕ) (hZ : 1 ≤ Z)
    (hB : B ≤ Z) (hd : d ≤ Z) (hn : n ≤ Z) (hu : u ≤ Z) (hJ : J ≤ Z)
    (hN : N ≤ Z) (hk : k ≤ Z) :
    markedServiceBound B d n u J N k ≤ 4000000*Z^8 := by
  have hm : markedServiceBound B d n u J N k ≤ markedServiceBound Z Z Z Z Z Z Z := by
    dsimp only [markedServiceBound,tableBound,Cost.literalBound,Cost.negativeBound,
      Cost.fetchBound,Cost.bytesBound,Cost.productBound,Cost.scaleBound,Cost.normalizeBound,
      MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
    gcongr
  apply hm.trans
  have he : markedServiceBound Z Z Z Z Z Z Z =
      40000*Z^8+280220*Z^7+806880*Z^6+1225837*Z^5+1033913*Z^4+
      455876*Z^3+81677*Z^2+400*Z+67 := by
    dsimp only [markedServiceBound,tableBound,Cost.literalBound,Cost.negativeBound,
      Cost.fetchBound,Cost.bytesBound,Cost.productBound,Cost.scaleBound,Cost.normalizeBound,
      MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
    ring
  rw [he]
  have hp (k : ℕ) (hk : k ≤ 8) : Z^k ≤ Z^8 := Nat.pow_le_pow_right hZ hk
  have h0 : 1 ≤ Z^8 := by simpa using hp 0 (by decide)
  have h1 : Z ≤ Z^8 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  omega

def expansionBound (b ml m sourceLength weightLength count : ℕ) : ℕ :=
  3+count*(HashInputProgram.Loop.termBudget b ml m sourceLength weightLength sourceLength+4)

theorem expansionBound_le (b ml m sourceLength weightLength count Z : ℕ) (hZ : 1 ≤ Z)
    (hb : b ≤ Z) (hml : ml ≤ Z) (hm : m ≤ Z) (hs : sourceLength ≤ Z)
    (hw : weightLength ≤ Z) (hc : count ≤ Z) :
    expansionBound b ml m sourceLength weightLength count ≤ 2000*Z^3 := by
  have h : expansionBound b ml m sourceLength weightLength count ≤ expansionBound Z Z Z Z Z Z := by
    dsimp only [expansionBound,HashInputProgram.Loop.termBudget,HashInputProgram.LoopDecode.budget]
    gcongr
  apply h.trans
  have he : expansionBound Z Z Z Z Z Z = 464*Z^3+586*Z^2+217*Z+3 := by
    dsimp only [expansionBound,HashInputProgram.Loop.termBudget,HashInputProgram.LoopDecode.budget]
    ring
  rw [he]
  have h0 : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  have h1 : Z ≤ Z^3 := by simpa using Nat.pow_le_pow_right hZ (show 1 ≤ 3 by decide)
  have h2 : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
