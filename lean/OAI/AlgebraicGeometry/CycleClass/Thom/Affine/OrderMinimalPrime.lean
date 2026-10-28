import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Order Minimal Prime -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.OrderMinimalPrime.Constructions

noncomputable section

/-! A nonzero affine regular function has nonzero order precisely at
the height-one primes containing it, which are its minimal primes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (a : R) (ha : a ≠ 0) (q : PrimeSpectrum R) (hq : q.asIdeal.height = 1)

local instance : q.asIdeal.IsPrime := q.isPrime

include ha hq

theorem mem_minimalPrimes_iff_mem :
    q.asIdeal ∈ (Ideal.span {a}).minimalPrimes ↔ a ∈ q.asIdeal := by
  constructor
  · intro h
    exact h.le (Ideal.subset_span (Set.mem_singleton a))
  · intro h
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h))
    let : P.IsPrime := hP.isPrime
    have hlow : 1 ≤ P.height :=
      (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ha)).trans (Ideal.height_mono hP.le)
    have he : P = q.asIdeal := Ideal.eq_of_le_of_height_le P hPq (hq.le.trans hlow)
    rwa [← he]

theorem schemeOrder_eq_zero_iff_not_mem :
    (Spec (.of R)).ord (PrincipalSchemeOrder.Constructions.affineFunction R a) q = 0 ↔ a ∉ q.asIdeal := by
  let S := Localization.AtPrime q.asIdeal
  let : Ring.KrullDimLE 1 S := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal S, hq]
    rfl)
  have hne : algebraMap R S a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective S q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  have hfin := Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hne)
  rw [PrincipalSchemeOrder.Constructions.schemeOrder_eq_localOrder R q hq a ha, Int.natCast_eq_zero, ENat.toNat_eq_zero,
    or_iff_left hfin, Ring.ord, Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
    Ideal.span_singleton_eq_top, IsLocalization.AtPrime.isUnit_to_map_iff S q.asIdeal a]
  rfl

theorem schemeOrder_ne_zero_iff_minimal :
    (Spec (.of R)).ord (PrincipalSchemeOrder.Constructions.affineFunction R a) q ≠ 0 ↔ q.asIdeal ∈ (Ideal.span {a}).minimalPrimes := by
  exact (not_congr (schemeOrder_eq_zero_iff_not_mem R a ha q hq)).trans
    (not_not.trans (mem_minimalPrimes_iff_mem R a ha q hq).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.OrderMinimalPrime.Constructions
