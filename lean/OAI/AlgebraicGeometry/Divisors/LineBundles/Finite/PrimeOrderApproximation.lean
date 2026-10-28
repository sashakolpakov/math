import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeUniformizers
import OAI.AlgebraicGeometry.Divisors.LineBundles.FractionOrderLaws
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Prime Order Approximation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeOrderApproximation.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual rational functions with Kronecker-delta orders at finitely many primes -/

variable {R ι : Type*} [CommRing R] [Finite ι]
    (P : ι → Ideal R) [∀ i, (P i).IsPrime]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, IsLocalization.AtPrime (A i) (P i)] [∀ i, IsDomain (A i)]
    [∀ i, IsDiscreteValuationRing (A i)]
    (hne : Pairwise fun i j => ¬ P i ≤ P j)
    (K : Type*) [Field K] [Algebra R K] [∀ i, Algebra (A i) K]
    [∀ i, IsScalarTower R (A i) K] [∀ i, IsFractionRing (A i) K]

theorem finitePrimeUniformizer_field_ne_zero (i : ι) :
    algebraMap R K (PrimeUniformizers.BundleCycles.finitePrimeUniformizer P A hne i) ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply R (A i) K]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (A i) K)).mpr
    (PrimeUniformizers.BundleCycles.finitePrimeUniformizer_irreducible P A hne i).ne_zero

def finitePrimeOrderUnit (i : ι) : Kˣ :=
  Units.mk0 (algebraMap R K (PrimeUniformizers.BundleCycles.finitePrimeUniformizer P A hne i))
    (finitePrimeUniformizer_field_ne_zero P A hne K i)

theorem finitePrimeOrderUnit_order_self (i : ι) :
    SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A i) (finitePrimeOrderUnit P A hne K i : K) = 1 := by
  change SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A i) (algebraMap R K (PrimeUniformizers.BundleCycles.finitePrimeUniformizer P A hne i)) = 1
  rw [IsScalarTower.algebraMap_apply R (A i) K]
  unfold SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder
  rw [Ring.ordFrac_irreducible (PrimeUniformizers.BundleCycles.finitePrimeUniformizer_irreducible P A hne i)]
  rfl

theorem finitePrimeOrderUnit_order_other (i j : ι) (hji : j ≠ i) :
    SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A j) (finitePrimeOrderUnit P A hne K i : K) = 0 := by
  change SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A j) (algebraMap R K (PrimeUniformizers.BundleCycles.finitePrimeUniformizer P A hne i)) = 0
  rw [IsScalarTower.algebraMap_apply R (A j) K]
  unfold SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder
  rw [Ring.ordFrac_of_isUnit (PrimeUniformizers.BundleCycles.finitePrimeUniformizer_isUnit P A hne i j hji)]
  rfl

end

/-! # LineBundleCycles: prescribed positive and negative orders at a finite family of prime divisors -/

open scoped BigOperators

variable {R ι : Type*} [CommRing R] [Finite ι]
    (P : ι → Ideal R) [∀ i, (P i).IsPrime]
    (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, IsLocalization.AtPrime (A i) (P i)] [∀ i, IsDomain (A i)]
    [∀ i, IsDiscreteValuationRing (A i)]
    (hne : Pairwise fun i j => ¬ P i ≤ P j)
    (K : Type*) [Field K] [Algebra R K] [∀ i, Algebra (A i) K]
    [∀ i, IsScalarTower R (A i) K] [∀ i, IsFractionRing (A i) K]

def finitePrimeOrderApproximation (n : ι → ℤ) : Kˣ :=
  letI := Fintype.ofFinite ι
  ∏ i, finitePrimeOrderUnit P A hne K i ^ n i

theorem finitePrimeOrderApproximation_order (n : ι → ℤ) (j : ι) :
    SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A j) (finitePrimeOrderApproximation P A hne K n : K) = n j := by
  classical
  let := Fintype.ofFinite ι
  apply Multiplicative.ofAdd.injective
  change FractionOrderLaws.BundleCycles.fractionFieldOrderHom (A j) (∏ i, finitePrimeOrderUnit P A hne K i ^ n i) =
    Multiplicative.ofAdd (n j)
  rw [map_prod, Finset.prod_eq_single j]
  · rw [map_zpow]
    change Multiplicative.ofAdd (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A j) (finitePrimeOrderUnit P A hne K j : K)) ^ n j = _
    rw [finitePrimeOrderUnit_order_self]
    change Multiplicative.ofAdd ((n j) * 1) = Multiplicative.ofAdd (n j)
    rw [mul_one]
  · intro i _ hij
    rw [map_zpow]
    change Multiplicative.ofAdd (SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A j) (finitePrimeOrderUnit P A hne K i : K)) ^ n i = 1
    rw [finitePrimeOrderUnit_order_other P A hne K i j hij.symm]
    exact one_zpow _
  · intro h
    exact (h (Finset.mem_univ _)).elim

include hne in
theorem exists_prescribed_finitePrimeOrders (n : ι → ℤ) :
    ∃ g : Kˣ, ∀ i, SurfaceRationalOrderIntersection.BundleCycles.fractionFieldOrder (A i) (g : K) = n i :=
  ⟨finitePrimeOrderApproximation P A hne K n,
    finitePrimeOrderApproximation_order P A hne K n⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeOrderApproximation.BundleCycles
