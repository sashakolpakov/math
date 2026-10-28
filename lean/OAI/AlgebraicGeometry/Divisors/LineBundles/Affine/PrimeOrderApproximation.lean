import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeOrderApproximation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.PointResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeSupport

/-! # Prime Order Approximation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeOrderApproximation.BundleCycles

noncomputable section

/-! # LineBundleCycles: prescribed actual scheme orders at finitely many normal codimension-one affine points -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]

local instance affineApproximation_fieldAlgebra : Algebra R (Spec (CommRingCat.of R)).functionField :=
  (StructureSheaf.toStalk R (genericPoint (Spec (CommRingCat.of R)))).hom.toAlgebra

local instance affineApproximation_stalkAlgebra (x : Spec (CommRingCat.of R)) :
    Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x

local instance affineApproximation_pointPrime (x : Spec (CommRingCat.of R)) : x.asIdeal.IsPrime :=
  (show PrimeSpectrum R from x).isPrime

local instance affineApproximation_stalkLocalization (x : Spec (CommRingCat.of R)) :
    IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk x) x.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R x

omit [IsNoetherianRing R] in
theorem affineApproximation_stalkField_tower (x : Spec (CommRingCat.of R)) :
    IsScalarTower R ((Spec (CommRingCat.of R)).presheaf.stalk x)
      (Spec (CommRingCat.of R)).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (StructureSheaf.toStalk_stalkSpecializes
      ((genericPoint_spec (Spec (CommRingCat.of R))).specializes trivial))).symm

omit [IsDomain R] in
theorem affineCodimensionOne_primes_incomparable {ι : Type*}
    (x : ι → Spec (CommRingCat.of R)) (hx : ∀ i, coheight (x i) = 1)
    (hinj : Function.Injective x) : Pairwise fun i j => ¬ (x i).asIdeal ≤ (x j).asIdeal := by
  intro i j hij hle
  let : (x i).asIdeal.IsPrime := (show PrimeSpectrum R from x i).isPrime
  have hi : (x i).asIdeal.height = 1 := by rw [idealHeight_eq_coheight, hx i]
  have hj : (x j).asIdeal.height = 1 := by rw [idealHeight_eq_coheight, hx j]
  have he := Ideal.eq_of_le_of_height_le (x i).asIdeal hle (hj.trans hi.symm).le
  exact hij (hinj (PrimeSpectrum.ext he))

theorem exists_affine_prescribed_orders {ι : Type*} [Finite ι]
    (x : ι → Spec (CommRingCat.of R)) (hx : ∀ i, coheight (x i) = 1)
    (hinj : Function.Injective x)
    [∀ i, IsIntegrallyClosed ((Spec (CommRingCat.of R)).presheaf.stalk (x i))]
    (n : ι → ℤ) :
    ∃ g : (Spec (CommRingCat.of R)).functionFieldˣ,
      ∀ i, (Spec (CommRingCat.of R)).ord (g : (Spec (CommRingCat.of R)).functionField) (x i) = n i := by
  let : ∀ i, (x i).asIdeal.IsPrime := fun i => (show PrimeSpectrum R from x i).isPrime
  let : ∀ i, IsDiscreteValuationRing ((Spec (CommRingCat.of R)).presheaf.stalk (x i)) :=
    fun i => Normal.PointResidue.BundleCycles.normal_stalk_isDVR (Spec (CommRingCat.of R)) (x i) (hx i)
  let : ∀ i, IsScalarTower R ((Spec (CommRingCat.of R)).presheaf.stalk (x i))
      (Spec (CommRingCat.of R)).functionField := fun i => affineApproximation_stalkField_tower (x i)
  obtain ⟨g, hg⟩ := LineBundles.Finite.PrimeOrderApproximation.BundleCycles.exists_prescribed_finitePrimeOrders (fun i => (x i).asIdeal)
    (fun i => (Spec (CommRingCat.of R)).presheaf.stalk (x i))
    (affineCodimensionOne_primes_incomparable x hx hinj) (Spec (CommRingCat.of R)).functionField n
  refine ⟨g, fun i => ?_⟩
  exact ((Spec (CommRingCat.of R)).ord_eq_ordHom_of_coheight_eq_one (hx i) _).trans (hg i)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.PrimeOrderApproximation.BundleCycles
