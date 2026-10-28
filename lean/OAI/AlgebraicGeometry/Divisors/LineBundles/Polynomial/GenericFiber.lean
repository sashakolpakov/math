import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.FieldPointDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationPointDivisor
import Mathlib.RingTheory.Localization.Algebra

/-! # Generic Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.GenericFiber.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: a generic-fiber point has a genuine rational equation with all generic-fiber coefficients prescribed -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local instance] Polynomial.algebra

def polynomialGenericFiberMap : Spec (.of (Polynomial K)) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (Polynomial K)))

variable [IsNoetherianRing R]

theorem polynomialGenericFiberDivisor_exists (p : Spec (.of (Polynomial K))) (hp : p.asIdeal ≠ ⊥) :
    ∃ g : (Spec (.of (Polynomial R))).functionField, g ≠ 0 ∧ ∀ q : Spec (.of (Polynomial K)),
      ((Spec (.of (Polynomial R))).ord g (polynomialGenericFiberMap R K q) : ℚ) =
        Finsupp.single p 1 q := by
  have : IsLocalization ((nonZeroDivisors R).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  obtain ⟨a, ha, hdiv⟩ := FieldPointDivisor.BundleCycles.polynomialFieldPoint_exists_principal K p hp
  have hs : (Scheme.ΓSpecIso (.of (Polynomial K))).inv a ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.ΓSpecIso (.of (Polynomial K))).symm.commRingCatIsoToRingEquiv.injective).mpr ha
  exact LocalizationPointDivisor.BundleCycles.localizationPointDivisor_lift (Polynomial R) (Polynomial K)
    ((nonZeroDivisors R).map Polynomial.C) p _
    (RegularDivisor.BundleCycles.globalFunctionFieldElement_ne_zero _ _ hs) hdiv

end

section

/-! # LineBundleCycles: the actual generic polynomial fiber consists exactly of primes contracting to zero -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local instance] Polynomial.algebra

omit [IsDomain R] in
theorem polynomialGenericFiberMap_injective : Function.Injective (polynomialGenericFiberMap R K) := by
  have : IsLocalization ((nonZeroDivisors R).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  exact PrimeSpectrum.localization_comap_injective (Polynomial K) ((nonZeroDivisors R).map Polynomial.C)

theorem polynomialGenericFiberMap_range_iff (p : Spec (.of (Polynomial R))) :
    p ∈ Set.range (polynomialGenericFiberMap R K) ↔ p.asIdeal.comap Polynomial.C = ⊥ := by
  have : IsLocalization ((nonZeroDivisors R).map Polynomial.C) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors R) K
  change p ∈ Set.range (PrimeSpectrum.comap (algebraMap (Polynomial R) (Polynomial K))) ↔ _
  rw [PrimeSpectrum.localization_comap_range (Polynomial K) ((nonZeroDivisors R).map Polynomial.C)]
  change Disjoint (((nonZeroDivisors R).map Polynomial.C) : Set (Polynomial R)) p.asIdeal ↔ _
  constructor
  · intro h
    apply bot_unique
    intro a ha
    apply Ideal.mem_bot.mpr
    by_contra hn
    exact Set.disjoint_left.mp h
      (Submonoid.mem_map_of_mem Polynomial.C (mem_nonZeroDivisors_iff_ne_zero.mpr hn)) ha
  · intro h
    apply Set.disjoint_left.mpr
    intro a ha hp
    obtain ⟨r, hr, rfl⟩ := ha
    have hz : r = 0 := Ideal.mem_bot.mp (h.le hp)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hz

omit [IsDomain R] in
theorem polynomialGenericFiberMap_nonzero (p : Spec (.of (Polynomial R)))
    (hp : p.asIdeal ≠ ⊥) (q : Spec (.of (Polynomial K))) (hq : polynomialGenericFiberMap R K q = p) :
    q.asIdeal ≠ ⊥ := by
  intro hqzero
  apply hp
  have h := congrArg (fun x : Spec (.of (Polynomial R)) => x.asIdeal) hq
  change Ideal.comap (algebraMap (Polynomial R) (Polynomial K)) q.asIdeal = p.asIdeal at h
  rw [hqzero] at h
  exact h.symm.trans (Ideal.comap_bot_of_injective _
    (Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)))

end

/-! # LineBundleCycles: a horizontal affine-line divisor differs from an actual principal divisor only over proper base supports -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem polynomialHorizontalPoint_relation (p : Spec (.of (Polynomial R)))
    (hp : p.asIdeal ≠ ⊥) (hbase : p.asIdeal.comap Polynomial.C = ⊥) :
    ∃ g : (Spec (.of (Polynomial R))).functionField, g ≠ 0 ∧
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g p = 1 ∧
      ∀ q ∈ (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g - Finsupp.single p 1).support,
        q.asIdeal.comap Polynomial.C ≠ ⊥ := by
  let K := FractionRing R
  obtain ⟨P, hP⟩ := (polynomialGenericFiberMap_range_iff R K p).mpr hbase
  obtain ⟨g, hg, hdiv⟩ := polynomialGenericFiberDivisor_exists R K P
    (polynomialGenericFiberMap_nonzero R K p hp P hP)
  have hpoint : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g p = 1 := by
    have h := hdiv P
    rw [hP, Finsupp.single_eq_same] at h
    exact h
  refine ⟨g, hg, hpoint, ?_⟩
  intro q hq hzero
  obtain ⟨Q, hQ⟩ := (polynomialGenericFiberMap_range_iff R K q).mpr hzero
  have hsingle : Finsupp.single p (1 : ℚ) q = Finsupp.single P 1 Q := by
    rw [← hP, ← hQ]
    exact Finsupp.single_apply_left (polynomialGenericFiberMap_injective R K) P Q 1
  have he : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of (Polynomial R))) g q = Finsupp.single p 1 q := by
    exact (congrArg (fun x => ((Spec (.of (Polynomial R))).ord g x : ℚ)) hQ).symm.trans
      ((hdiv Q).trans hsingle.symm)
  exact Finsupp.mem_support_iff.mp hq (by rw [Finsupp.sub_apply, he, sub_self])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.GenericFiber.BundleCycles
