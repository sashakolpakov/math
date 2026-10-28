import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain

/-! # Smooth Normal -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormal.Constructions

noncomputable section

/-!
# DegreeTwo: smooth local rings over fields are integrally closed

The actual integral-closure comparison for an etale algebra gives integral
closure in its reduced Artinian generic fiber. Locality forces that fiber
to be a field, so integral closure there implies ordinary integral closure.
The smooth prime-localization chart then gives the desired local normality.
-/

open scoped TensorProduct

universe u v w

/-- A local ring integrally closed in a reduced Artinian extension forces
that extension to be a field: all idempotents lift and are trivial. -/
theorem isField_of_local_integrallyClosedIn_artinian
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsArtinianRing B] [IsReduced B] [Algebra A B]
    [IsIntegrallyClosedIn A B] : IsField B := by
  have hinj := (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn A B)).1
  let : Nontrivial B := hinj.nontrivial
  apply Foundations.Scheme.DomainFromGenericFiber.isField_of_artinian_reduced_idempotents_trivial B
  intro b hb
  have hbint : IsIntegral A b := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simp [pow_two, hb.eq]
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hbint
  have haidem : IsIdempotentElem a := by
    change a * a = a
    apply hinj
    rw [map_mul, ha]
    exact hb
  rcases Foundations.Scheme.DomainFromGenericFiber.idempotent_eq_zero_or_one_of_local haidem with h0 | h1
  · left
    rw [← ha, h0, map_zero]
  · right
    rw [← ha, h1, map_one]

/-- Local localizations of etale algebras over normal domains are integrally
closed; no normality premise is imposed on the localized ring. -/
theorem isIntegrallyClosed_of_localization_of_etale
    (R : Type u) (S : Type v) (A : Type w)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.Etale R S]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] (M : Submonoid S) [IsLocalization M A] : IsIntegrallyClosed A := by
  let K := FractionRing R
  let B := A ⊗[R] K
  let C := K ⊗[R] A
  let : Module.Flat S A := IsLocalization.flat A M
  let : Module.Flat R A := Module.Flat.trans R S A
  let : Algebra.FormallyUnramified S A := Algebra.FormallyUnramified.of_isLocalization M
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
  let : IsIntegrallyClosedIn A B :=
    Foundations.Scheme.TensorIntegralClosure.isIntegrallyClosedIn_tensor_of_comparison_surjective hc.surjective
  let : Field B := (isField_of_local_integrallyClosedIn_artinian A B).toField
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (isIntegrallyClosedIn_iff.mp (inferInstance : IsIntegrallyClosedIn A B)).1
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn A B

/-- The actual prime localization of a smooth algebra over a field is normal. -/
theorem isIntegrallyClosed_localizationAtPrime_of_isSmoothAt
    (K : Type u) (S : Type v) [Field K] [CommRing S] [Algebra K S]
    [Algebra.FinitePresentation K S] (p : Ideal S) [p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsIntegrallyClosed (Localization.AtPrime p) := by
  obtain ⟨f, hfp, n, hPB, _, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let P := MvPolynomial (Fin n) K
  let B := Localization.Away f
  let A := Localization.AtPrime p
  let : Algebra P B := hPB
  let : Algebra.IsStandardEtale P B := hEtale
  have hle : Submonoid.powers f ≤ p.primeCompl := Submonoid.powers_le.mpr hfp
  let : Algebra B A := IsLocalization.localizationAlgebraOfSubmonoidLe
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsScalarTower S B A := IsLocalization.localization_isScalarTower_of_submonoid_le
    B A (Submonoid.powers f) p.primeCompl hle
  let : IsLocalization (p.primeCompl.map (algebraMap S B)) A :=
    IsLocalization.isLocalization_of_submonoid_le B A (Submonoid.powers f) p.primeCompl hle
  let : Algebra P A := ((algebraMap B A).comp (algebraMap P B)).toAlgebra
  let : IsScalarTower P B A := IsScalarTower.of_algebraMap_eq' rfl
  exact isIntegrallyClosed_of_localization_of_etale P B A (p.primeCompl.map (algebraMap S B))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothNormal.Constructions
