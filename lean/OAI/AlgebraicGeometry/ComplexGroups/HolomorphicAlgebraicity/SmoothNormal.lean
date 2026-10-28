import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # Smooth Normal -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SmoothNormal.Constructions.Algebraization

noncomputable section

/-!
# Integral closedness of local rings of smooth complex algebras

The integral-closure comparison for an étale localization puts every integral
generic-fiber element in the local ring. Lifting idempotents makes that generic
fiber a field, so the local ring is integrally closed.
-/

open _root_.AlgebraicGeometry
open scoped TensorProduct

theorem isField_of_local_artinian_reduced_extension
    {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsArtinianRing B] [IsReduced B]
    (f : A →+* B) (hf : Function.Injective f)
    (hlift : ∀ b : B, IsIdempotentElem b → ∃ a : A, f a = b) : IsField B := by
  let : Nontrivial B := hf.nontrivial
  apply Foundations.Scheme.DomainFromGenericFiber.isField_of_artinian_reduced_idempotents_trivial B
  intro b hb
  obtain ⟨a, ha⟩ := hlift b hb
  have haidem : IsIdempotentElem a := by
    change a * a = a
    apply hf
    rw [map_mul, ha]
    exact hb
  rcases Foundations.Scheme.DomainFromGenericFiber.idempotent_eq_zero_or_one_of_local haidem with h0 | h1
  · left
    rw [← ha, h0, map_zero]
  · right
    rw [← ha, h1, map_one]

theorem isIntegrallyClosed_of_localization_of_etale
    (R S A : Type*)
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
  have hinj : Function.Injective (algebraMap A B) :=
    Algebra.TensorProduct.includeLeft_injective (S := A) (IsFractionRing.injective R K)
  have hfield : IsField B := by
    apply isField_of_local_artinian_reduced_extension (algebraMap A B) hinj
    intro z hz
    apply Foundations.Scheme.TensorIntegralClosure.exists_tensorLeft_eq_of_isIntegral hc.surjective z
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simp [pow_two, hz.eq]
  let : Field B := hfield.toField
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let : IsIntegrallyClosedIn A B := Foundations.Scheme.TensorIntegralClosure.isIntegrallyClosedIn_tensor_of_comparison_surjective hc.surjective
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn A B

theorem isIntegrallyClosed_localizationAtPrime_of_smooth
    (K S : Type*) [Field K] [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    (p : Ideal S) [p.IsPrime] : IsIntegrallyClosed (Localization.AtPrime p) := by
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

theorem isIntegrallyClosed_of_smooth_domain
    (K S : Type*) [Field K] [CommRing S] [IsDomain S]
    [Algebra K S] [Algebra.Smooth K S] : IsIntegrallyClosed S := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ _
  exact isIntegrallyClosed_localizationAtPrime_of_smooth K S p

theorem isIntegrallyClosed_affineOpen_of_smooth_integral
    (X : CategoryTheory.Over Foundations.Scheme.ProjectiveSpace.complexBase) [AlgebraicGeometry.IsIntegral X.left]
    [AlgebraicGeometry.Smooth X.hom] (U : X.left.Opens) (hU : AlgebraicGeometry.IsAffineOpen U)
    [Nonempty U] : IsIntegrallyClosed Γ(X.left, U) := by
  let : Algebra.Smooth ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) :=
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
  exact isIntegrallyClosed_of_smooth_domain ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SmoothNormal.Constructions.Algebraization
