import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullbackCoherence

/-! # Scheme Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SchemeIso

noncomputable section

/-! Scheme isomorphisms induce equivalences on the original integral and rational crystalline cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullback OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallinePullbackCoherence

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {X Y : Over (Spec (CommRingCat.of k))} [IsSeparated X.hom] [IsSeparated Y.hom]
  (e : X ≅ Y) (i : ℕ)

def integral : Witt.Crystalline.integralCohomology p k Y i ≃ₗ[WittVector p k] Witt.Crystalline.integralCohomology p k X i where
  toLinearMap := PeriodInvariants.CrystallinePullback.integralPullback p k e.hom i
  invFun := PeriodInvariants.CrystallinePullback.integralPullback p k e.inv i
  left_inv x := by
    refine (PeriodInvariants.CrystallinePullbackCoherence.integralPullback_comp p k e.inv e.hom i x).trans ?_
    rw [e.inv_hom_id]
    exact PeriodInvariants.CrystallinePullbackCoherence.integralPullback_id p k i x
  right_inv x := by
    refine (PeriodInvariants.CrystallinePullbackCoherence.integralPullback_comp p k e.hom e.inv i x).trans ?_
    rw [e.hom_inv_id]
    exact PeriodInvariants.CrystallinePullbackCoherence.integralPullback_id p k i x

def rational : Witt.Crystalline.rationalCohomology p k Y i ≃ₗ[FractionRing (WittVector p k)]
    Witt.Crystalline.rationalCohomology p k X i where
  toLinearMap := PeriodInvariants.CrystallinePullback.rationalPullback p k e.hom i
  invFun := PeriodInvariants.CrystallinePullback.rationalPullback p k e.inv i
  left_inv x := by
    refine (PeriodInvariants.CrystallinePullbackCoherence.rationalPullback_comp p k e.inv e.hom i x).trans ?_
    rw [e.inv_hom_id]
    exact PeriodInvariants.CrystallinePullbackCoherence.rationalPullback_id p k i x
  right_inv x := by
    refine (PeriodInvariants.CrystallinePullbackCoherence.rationalPullback_comp p k e.hom e.inv i x).trans ?_
    rw [e.hom_inv_id]
    exact PeriodInvariants.CrystallinePullbackCoherence.rationalPullback_id p k i x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SchemeIso
