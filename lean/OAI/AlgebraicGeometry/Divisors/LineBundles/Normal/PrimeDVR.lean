import OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.AuxiliaryParameter
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Field

/-! # Prime DVR -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PrimeDVR.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual DVR at a principal divisor on a normal ring

The height is exactly one by the principal ideal theorem. Normality
localizes, and the one-dimensional normal Noetherian local ring is a
DVR. A numerator of a local uniformizer gives a uniformizer coming
from an actual element of the original ring.
-/

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem minimalPrincipalPrime_height_eq_one (r : R) (hr : r ≠ 0)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {r}).minimalPrimes) : P.height = 1 := by
  have hPbot : P ≠ ⊥ := by
    intro he
    have hp := hP.le (Ideal.subset_span (Set.mem_singleton r))
    rw [he, Ideal.mem_bot] at hp
    exact hr hp
  exact le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {r}) P hP)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hPbot))

theorem normalMinimalPrime_isDVR [IsIntegrallyClosed R] (r : R) (hr : r ≠ 0)
    (P : Ideal R) [P.IsPrime] (hP : P ∈ (Ideal.span {r}).minimalPrimes) :
    IsDiscreteValuationRing (Localization P.primeCompl) := by
  let A := Localization P.primeCompl
  have hS : P.primeCompl ≤ nonZeroDivisors R := by
    intro x hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (fun he => hx (he ▸ P.zero_mem))
  let normalPrimeClosure : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A P.primeCompl hS
  have hdim : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P A, minimalPrincipalPrime_height_eq_one r hr P hP]
    rfl
  let normalPrimeDimension : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim.le
  let normalPrimeDimensionOne : Ring.DimensionLEOne A := ⟨fun hn hp => hp.isMaximal_of_ne_bot hn⟩
  let normalPrimeDedekind : IsDedekindDomain A :=
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }
  have hfield : ¬ IsField A := by
    intro hf
    have he := (ringKrullDim_eq_zero_of_isField hf).symm.trans hdim
    exact (by decide : (0 : WithBot ℕ∞) ≠ 1) he
  exact ((IsDiscreteValuationRing.TFAE A hfield).out 1 3).mpr normalPrimeDedekind

omit [IsNoetherianRing R] in
theorem exists_originalRing_uniformizer (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization P.primeCompl)] :
    ∃ t : R, t ≠ 0 ∧ Irreducible (algebraMap R (Localization P.primeCompl) t) := by
  let A := Localization P.primeCompl
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨t, s, hs⟩ := IsLocalization.exists_mk'_eq P.primeCompl π
  have ht : algebraMap R A t = π * algebraMap R A s := by
    rw [← hs]
    exact (IsLocalization.mk'_spec A t s).symm
  have hirr : Irreducible (algebraMap R A t) := by
    rw [ht]
    exact (irreducible_mul_isUnit (IsLocalization.map_units A s)).mpr hπ
  exact ⟨t, fun he => hirr.ne_zero (he ▸ map_zero _), hirr⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PrimeDVR.BundleCycles
