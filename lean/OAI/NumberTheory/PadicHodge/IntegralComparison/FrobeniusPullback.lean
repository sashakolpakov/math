import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PullbackPowers
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.CrystallineFrobenius
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Iteration

/-! # Frobenius Pullback -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FrobeniusPullback.Q

noncomputable section

/-! The original crystalline q-Frobenius and every power are the actual geometric pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (a : ℕ) (hcard : Fintype.card k = p ^ a)

def endomorphism : End X :=
  Over.homMk (BigCrystallineFrobenius.schemeFrobenius p k X a)
    (Global.FrobeniusGeometry.qFrobenius_over p Fact.out k X.hom a hcard)

theorem power_left (r : ℕ) : (endomorphism p k X a hcard ^ r).left =
    Global.FrobeniusGeometry.qFrobenius p Fact.out k X.hom (a * r) := by
  have h := (Functor.mapEnd X (Over.forget (Spec (CommRingCat.of k)))).map_pow (endomorphism p k X a hcard) r
  exact h.trans (Frobenius.Iteration.qFrobenius_pow p Fact.out k X.hom a r)

variable [IsSeparated X.hom]

theorem integral (i : ℕ) : Global.CrystallineFrobenius.integralFrobenius p k X a hcard i =
    PeriodInvariants.CrystallinePullback.integralPullback p k (endomorphism p k X a hcard) i := rfl

theorem rational (i : ℕ) : Global.CrystallineFrobenius.rationalFrobenius p k X a hcard i =
    PeriodInvariants.CrystallinePullback.rationalPullback p k (endomorphism p k X a hcard) i := rfl

theorem rational_power (i r : ℕ) : Global.CrystallineFrobenius.rationalFrobenius p k X a hcard i ^ r =
    PeriodInvariants.CrystallinePullback.rationalPullback p k (endomorphism p k X a hcard ^ r) i := by
  rw [rational]
  exact (Crystalline.PullbackPowers.rational p k (endomorphism p k X a hcard) i r).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FrobeniusPullback.Q
