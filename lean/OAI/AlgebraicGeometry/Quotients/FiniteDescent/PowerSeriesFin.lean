import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesNe
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.WeierstrassPrimeIs
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! # Power Series Fin -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesFin.Construction.PowerSeriesFactorial

/-! Unique factorization for formal power series over an infinite field. -/

variable (K : Type*) [Field K] [Infinite K]

theorem fin (n : ℕ) : UniqueFactorizationMonoid (MvPowerSeries (Fin n) K) := by
  induction n with
  | zero =>
    exact (MvPowerSeries.isEmptyEquiv (Fin 0) K).symm.toRingEquiv.toMulEquiv
      |>.uniqueFactorizationMonoid inferInstance
  | succ n ih =>
    have : IsDomain (MvPowerSeries (Fin n) K) := NoZeroDivisors.to_isDomain _
    have : IsDomain (MvPowerSeries (Fin (n + 1)) K) := NoZeroDivisors.to_isDomain _
    have : UniqueFactorizationMonoid (MvPowerSeries (Fin n) K) := ih
    have : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) K))
        (MvPowerSeries (Fin n) K) := PowerSeriesIs.Construction.PowerSeriesLocal.isAdicComplete
    refine { toWellFounded := inferInstance, irreducible_iff_prime := ?_ }
    intro f
    refine ⟨fun hf => ?_, fun hf => hf.irreducible⟩
    obtain ⟨a, ha⟩ := PowerSeriesNe.Construction.PowerSeriesRegularDirection.exists_shear_reduction_ne_zero f hf.ne_zero
    let e := (PowerSeriesSubst.Construction.PowerSeriesShear.equiv a).trans (MvPowerSeries.finSuccEquiv K n)
    have hi : Irreducible (e f) := (MulEquiv.irreducible_iff e.toMulEquiv).mpr hf
    have hp : Prime (e f) := WeierstrassPrimeIs.Construction.WeierstrassPrime.prime_of_irreducible_of_reduction_ne_zero ha hi
    exact (MulEquiv.prime_iff e.toMulEquiv).mp hp

theorem finite_variables (σ : Type*) [Finite σ] :
    UniqueFactorizationMonoid (MvPowerSeries σ K) := by
  classical
  let := Fintype.ofFinite σ
  let e := MvPowerSeries.renameEquiv K (Fintype.equivFin σ)
  exact e.symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid (fin K _)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesFin.Construction.PowerSeriesFactorial
