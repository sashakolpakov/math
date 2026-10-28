import OAI.AlgebraicGeometry.Foundations.Scheme.TensorIntegralClosure
import OAI.AlgebraicGeometry.Foundations.Scheme.DomainFromGenericFiber
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Flat.Localization

/-! # Etale Local Domain -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.EtaleLocalDomain

noncomputable section

/-!
# Localizations of étale algebras over an integrally closed domain

An étale algebra has a reduced Artinian generic fiber. Smooth base change
commutes with integral closure, and this comparison remains bijective after
arbitrary localization. Hence all generic-fiber idempotents lift. A local
source which embeds in that generic fiber is therefore a domain.
-/

open scoped TensorProduct

universe u v w

/-- Every local localization of an étale algebra over an integrally closed
domain is a domain. The integral-closure property of the local ring is
derived from smooth base change and localization, not assumed. -/
theorem isDomain_of_localization_of_etale
    (R : Type u) (S : Type v) (A : Type w)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (M : Submonoid S) [IsLocalization M A] : IsDomain A := by
  let K := FractionRing R
  let B := A ⊗[R] K
  let C := K ⊗[R] A
  let : Module.Flat S A := IsLocalization.flat A M
  let : Module.Flat R A := Module.Flat.trans R S A
  let : Algebra.FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_isLocalization M
  let : Algebra.FormallyUnramified R A := Algebra.FormallyUnramified.comp R S A
  let : Algebra.EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A M
  let : Algebra.EssFiniteType R A := Algebra.EssFiniteType.comp R S A
  let : Module.Finite K C := Algebra.FormallyUnramified.finite_of_free K C
  let : IsArtinianRing C := IsArtinianRing.of_finite K C
  let : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field K C
  let : IsArtinianRing B := (Algebra.TensorProduct.comm R K A).toRingEquiv.isArtinianRing
  let : IsReduced B := isReduced_of_injective
    (Algebra.TensorProduct.comm R A K).toRingHom (Algebra.TensorProduct.comm R A K).injective
  have hc : Function.Bijective (TensorProduct.toIntegralClosure R A K) :=
    TensorProduct.toIntegralClosure_bijective_of_tower
      (R := R) (S := S) (T := A) (B := K)
      TensorProduct.toIntegralClosure_bijective_of_smooth
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization M)
  apply DomainFromGenericFiber.isDomain_of_local_of_artinian_reduced_extension (algebraMap A B)
    (Algebra.TensorProduct.includeLeft_injective (S := A) (IsFractionRing.injective R K))
  intro z hz
  apply TensorIntegralClosure.exists_tensorLeft_eq_of_isIntegral hc.surjective z
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
  simp [pow_two, hz.eq]

/-- In particular, every prime localization of such an étale algebra is a
domain. -/
theorem isDomain_atPrime_of_etale
    (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (p : Ideal S) [p.IsPrime] : IsDomain (Localization.AtPrime p) :=
  isDomain_of_localization_of_etale R S (Localization.AtPrime p) p.primeCompl

end

end OAI.AlgebraicGeometry.Foundations.Scheme.EtaleLocalDomain
