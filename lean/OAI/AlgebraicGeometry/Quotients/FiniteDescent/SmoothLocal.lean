import OAI.AlgebraicGeometry.Quotients.FiniteDescent.EtalePolynomial
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Smooth Local -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothLocal.Construction.SmoothLocalFactorial

noncomputable section

/-! Local factoriality of smooth algebras at rational points over an infinite field. -/

variable {K S : Type*} [Field K] [Infinite K] [CommRing S] [Algebra K S]

instance pointKernel_isPrime (e : S →ₐ[K] K) : (RingHom.ker e).IsPrime :=
  RingHom.ker_isPrime e

theorem at_rational_point [Algebra.Smooth K S] (e : S →ₐ[K] K) :
    UniqueFactorizationMonoid (Localization.AtPrime (RingHom.ker e)) := by
  let p := RingHom.ker e
  obtain ⟨f, hfp, n, hPB, hKPB, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  let B := Localization.Away f
  let A := Localization.AtPrime p
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let : Algebra P B := hPB
  have : IsScalarTower K P B := hKPB
  have : Algebra.IsStandardEtale P B := hEtale
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe
    B A (Submonoid.powers f) p.primeCompl hle
  have : IsScalarTower S B A := IsLocalization.localization_isScalarTower_of_submonoid_le
    B A (Submonoid.powers f) p.primeCompl hle
  have : IsLocalization (p.primeCompl.map (algebraMap S B)) A :=
    IsLocalization.isLocalization_of_submonoid_le
      B A (Submonoid.powers f) p.primeCompl hle
  let : Algebra P A := ((algebraMap B A).comp (algebraMap P B)).toAlgebra
  have : IsScalarTower P B A := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq fun k => by
    change algebraMap K A k = algebraMap B A (algebraMap P B (algebraMap K P k))
    rw [← IsScalarTower.algebraMap_apply K P B, IsScalarTower.algebraMap_apply K S B,
      ← IsScalarTower.algebraMap_apply S B A]
    exact IsScalarTower.algebraMap_apply K S A k
  have : Algebra.FormallyEtale B A :=
    Algebra.FormallyEtale.of_isLocalization (p.primeCompl.map (algebraMap S B))
  have : Algebra.FormallyEtale P A := Algebra.FormallyEtale.comp P B A
  have : Algebra.EssFiniteType B A :=
    Algebra.EssFiniteType.of_isLocalization A (p.primeCompl.map (algebraMap S B))
  have : Algebra.EssFiniteType P A := Algebra.EssFiniteType.comp P B A
  have hu (s : p.primeCompl) : IsUnit (e s) := isUnit_iff_ne_zero.mpr s.2
  let eA : A →ₐ[K] K := IsLocalization.liftAlgHom hu
  have heA : RingHom.ker eA = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective eA
      (fun k => ⟨algebraMap K A k, eA.commutes k⟩))
  exact EtalePolynomial.Construction.EtalePolynomialFactorial.of_point n eA heA

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothLocal.Construction.SmoothLocalFactorial
