import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullbackCoherence

/-! # Pullback Powers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PullbackPowers

noncomputable section

/-! Powers of geometric endomorphisms act by the corresponding powers on original crystalline cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullbackCoherence

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X : Over (Spec (CommRingCat.of k))} [IsSeparated X.hom] (g : End X) (i : ℕ)

theorem integral (r : ℕ) : PeriodInvariants.CrystallinePullback.integralPullback p k (g ^ r) i = PeriodInvariants.CrystallinePullback.integralPullback p k g i ^ r := by
  induction r with
  | zero =>
    apply LinearMap.ext
    intro x
    exact PeriodInvariants.CrystallinePullbackCoherence.integralPullback_id p k i x
  | succ r ih =>
    rw [pow_succ, End.mul_def, pow_succ']
    apply LinearMap.ext
    intro x
    exact (PeriodInvariants.CrystallinePullbackCoherence.integralPullback_comp p k g (g ^ r) i x).symm.trans
      (congrArg (PeriodInvariants.CrystallinePullback.integralPullback p k g i) (congrArg (fun f => f x) ih))

theorem rational (r : ℕ) : PeriodInvariants.CrystallinePullback.rationalPullback p k (g ^ r) i = PeriodInvariants.CrystallinePullback.rationalPullback p k g i ^ r := by
  induction r with
  | zero =>
    apply LinearMap.ext
    intro x
    exact PeriodInvariants.CrystallinePullbackCoherence.rationalPullback_id p k i x
  | succ r ih =>
    rw [pow_succ, End.mul_def, pow_succ']
    apply LinearMap.ext
    intro x
    exact (PeriodInvariants.CrystallinePullbackCoherence.rationalPullback_comp p k g (g ^ r) i x).symm.trans
      (congrArg (PeriodInvariants.CrystallinePullback.rationalPullback p k g i) (congrArg (fun f => f x) ih))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PullbackPowers
