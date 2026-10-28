import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgramBoundsMultiplier

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

theorem totalEnvelope_mono (B d n u J N L S : ℕ)
    (hB : B ≤ S) (hd : d ≤ S) (hn : n ≤ S) (hu : u ≤ S) (hJ : J ≤ S) (hN : N ≤ S) (hL : L ≤ S) :
    totalEnvelope B d n u J N L ≤ totalEnvelope S S S S S S S := by
  dsimp only [totalEnvelope,prepareEnvelope,arithmeticEnvelope,complementEnvelope,
    scaleStepEnvelope,normalizeStepEnvelope,applyEnvelope,loopEnvelope,
    quadraticEnvelope,accumulatorEnvelope,wordEnvelope,mulEnvelope,addEnvelope,
    byteCapacity,MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
  gcongr

theorem totalEnvelope_diagonal (S : ℕ) :
    totalEnvelope S S S S S S S =
      120000*S^8+680660*S^7+1660420*S^6+2270665*S^5+1901221*S^4+
        987023*S^3+298918*S^2+42025*S+304 := by
  dsimp only [totalEnvelope,prepareEnvelope,arithmeticEnvelope,complementEnvelope,
    scaleStepEnvelope,normalizeStepEnvelope,applyEnvelope,loopEnvelope,
    quadraticEnvelope,accumulatorEnvelope,wordEnvelope,mulEnvelope,addEnvelope,
    byteCapacity,MomentsProgram.Product.stepEnvelope,MomentsProgram.Dictionary.codeBranchBudget]
  ring

theorem totalEnvelope_diagonal_le (S : ℕ) (hS : 1 ≤ S) :
    totalEnvelope S S S S S S S ≤ 8000000*S^8 := by
  have hp (k : ℕ) (hk : k ≤ 8) : S^k ≤ S^8 := Nat.pow_le_pow_right hS hk
  have h0 : 1 ≤ S^8 := by simpa using hp 0 (by decide)
  have h1 : S ≤ S^8 := by simpa using hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  rw [totalEnvelope_diagonal]
  omega

/-- One fixed polynomial, with degree and coefficient independent of all
formula and ring parameters, bounds the complete measured application. -/
theorem totalEnvelope_le_power (B d n u J N L : ℕ) :
    totalEnvelope B d n u J N L ≤ 8000000*(B+d+n+u+J+N+L+1)^8 := by
  exact (totalEnvelope_mono B d n u J N L (B+d+n+u+J+N+L+1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
    (totalEnvelope_diagonal_le _ (by omega))


/-- The exact native setup and coefficient loop, including the compiled halt,
fit the same fixed polynomial. The list has precisely `t` degree-two digits. -/
theorem totalCost_coefficient_power {p t n d : ℕ} [Fact p.Prime]
    (ctx : Steps.Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J)
    (minus : RingProgram.Code (SubexpQuarticRing.Word (SubexpLiftRing.baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) :
    Multiplier.prepareCost ctx minus h one+
      Steps.applyLoopCost ctx h (Multiplier.prepared ctx minus h one)
        (List.ofFn (coefficientTriple t code))
        (Squarefree.encodeIndex (Multiplier.uKey n))+1 ≤
      8000000*(SubexpLiftRing.baseWidth p t+d+n+ctx.u+ctx.J+
        capacity vars ctx.u ctx.J+t+1)^8 := by
  exact (totalCost_coefficient_le ctx vars hu hJ minus h one hh ho code).trans
    (totalEnvelope_le_power _ _ _ _ _ _ _)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
