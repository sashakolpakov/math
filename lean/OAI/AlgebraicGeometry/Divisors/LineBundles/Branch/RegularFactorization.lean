import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PrimeDVR
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Regular Factorization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.RegularFactorization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: DVR factorization with denominators in the original ring

A local unit is represented by a numerator and denominator outside P.
Clearing that denominator gives s*a = u*t^m in the original domain,
and m is proved to be the actual order at P.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
theorem localUnit_originalRing_fraction (P : Ideal R) [P.IsPrime]
    (v : (Localization P.primeCompl)ˣ) :
    ∃ u s : R, u ∉ P ∧ s ∉ P ∧
      algebraMap R (Localization P.primeCompl) u =
        v * algebraMap R (Localization P.primeCompl) s := by
  let A := Localization P.primeCompl
  obtain ⟨u, s, hs⟩ := IsLocalization.exists_mk'_eq P.primeCompl (v : A)
  have hu : algebraMap R A u = v * algebraMap R A s := by
    rw [← hs]
    exact (IsLocalization.mk'_spec A u s).symm
  have huunit : IsUnit (algebraMap R A u) := hu ▸ v.isUnit.mul (IsLocalization.map_units A s)
  exact ⟨u, s, (IsLocalization.AtPrime.isUnit_to_map_iff A P u).mp huunit, s.2, hu⟩

theorem branchRegular_factorization (P : Ideal R) [P.IsPrime]
    [IsDiscreteValuationRing (Localization P.primeCompl)]
    (t : R) (ht : Irreducible (algebraMap R (Localization P.primeCompl) t))
    (a : R) (ha : a ≠ 0) :
    ∃ (m : ℕ) (u s : R), u ∉ P ∧ s ∉ P ∧ s * a = u * t ^ m ∧
      Ring.ord (Localization P.primeCompl) (algebraMap R (Localization P.primeCompl) a) = m := by
  let A := Localization P.primeCompl
  have hinj := IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  have haA : algebraMap R A a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible haA ht
  obtain ⟨u, s, huP, hsP, hus⟩ := localUnit_originalRing_fraction P v
  refine ⟨m, u, s, huP, hsP, ?_, ?_⟩
  · apply hinj
    rw [map_mul, map_mul, map_pow, hv, hus]
    ring
  · rw [hv, Ring.ord_mul_of_isUnit_left v.isUnit,
      Ring.ord_pow (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero), Ring.ord_of_irreducible ht]
    simp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.RegularFactorization.BundleCycles
