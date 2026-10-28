import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

/-! # Order Positive -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.OrderPositive

noncomputable section

/-! A nonzero equation has strictly positive order at every height-one
prime containing it, including singular and nonnormal localizations. -/

theorem ord_eq_zero_iff_isUnit (R : Type*) [CommRing R] (r : R) :
    Ring.ord R r = 0 ↔ IsUnit r := by
  rw [Ring.ord, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]

theorem weight_pos (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : PrimeSpectrum R) (hp : p.asIdeal.height = 1) (r : R) (hr : r ≠ 0) (hrp : r ∈ p.asIdeal) :
    0 < CanonicalSurfaceReciprocity.weight R p r := by
  let S := Localization.AtPrime p.asIdeal
  have hm : (IsLocalRing.maximalIdeal S).height = 1 := by
    rw [← IsLocalization.height_under p.asIdeal.primeCompl, Localization.AtPrime.under_maximalIdeal, hp]
  let : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr (by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm]
    rfl)
  have hi : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S p.asIdeal.primeCompl_le_nonZeroDivisors
  have hrS : algebraMap R S r ≠ 0 := (map_ne_zero_iff _ hi).mpr hr
  have hn : Ring.ord S (algebraMap R S r) ≠ 0 := by
    intro hz
    have hu := (ord_eq_zero_iff_isUnit S _).mp hz
    have hmem : algebraMap R S r ∈ IsLocalRing.maximalIdeal S := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hrp
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hmem
  have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hrS)
  have hnat : (Ring.ord S (algebraMap R S r)).toNat ≠ 0 := by
    intro hz
    apply hn
    rw [← ENat.natCast_toNat hfin, hz, Nat.cast_zero]
  change 0 < ((Ring.ord S (algebraMap R S r)).toNat : ℚ)
  exact_mod_cast Nat.pos_of_ne_zero hnat

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.OrderPositive
