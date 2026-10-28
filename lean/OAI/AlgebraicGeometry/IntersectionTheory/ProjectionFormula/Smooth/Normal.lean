import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothLocalDomain
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Normal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Normal

noncomputable section

/-! Normality of actual smooth local rings over a field. The proof uses
étale polynomial charts and the genuine integral-closure base-change map. -/

set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v w

theorem localization_etale_integrallyClosed
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
  have hi : Function.Injective (algebraMap A B) :=
    Algebra.TensorProduct.includeLeft_injective (S := A) (IsFractionRing.injective R K)
  let : Nontrivial B := hi.nontrivial
  have hfield : IsField B := Foundations.Scheme.DomainFromGenericFiber.isField_of_artinian_reduced_idempotents_trivial B (by
    intro b hb
    have hbint : IsIntegral A b := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
      simp [pow_two, hb.eq]
    obtain ⟨a, ha⟩ := Foundations.Scheme.TensorIntegralClosure.exists_tensorLeft_eq_of_isIntegral hc.surjective b hbint
    have ha' : algebraMap A B a = b := ha
    have haidem : IsIdempotentElem a := by
      apply hi
      simpa only [map_mul, ha'] using hb.eq
    rcases Foundations.Scheme.DomainFromGenericFiber.idempotent_eq_zero_or_one_of_local haidem with h0 | h1
    · exact Or.inl (by rw [← ha, h0, map_zero])
    · exact Or.inr (by rw [← ha, h1, map_one]))
  let : Field B := hfield.toField
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hi
  let : IsIntegrallyClosedIn A B :=
    Foundations.Scheme.TensorIntegralClosure.isIntegrallyClosedIn_tensor_of_comparison_surjective hc.surjective
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn A B

theorem localizationAtPrime_smooth_integrallyClosed
    (K : Type u) (S : Type v) [Field K] [CommRing S] [Algebra K S]
    [Algebra.Smooth K S] (p : Ideal S) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
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
  exact localization_etale_integrallyClosed P B A (p.primeCompl.map (algebraMap S B))

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem stalk_integrallyClosed {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  let := Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let := Foundations.Scheme.AffineOpenSmooth.specSectionScalarAlgebra_smooth f U hU
  let p := hU.primeIdealOf ⟨x, hx⟩
  let : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    localizationAtPrime_smooth_integrallyClosed K Γ(X, U) p.asIdeal
  let : IsIntegrallyClosed ((Spec Γ(X, U)).presheaf.stalk p) :=
    IsIntegrallyClosed.of_equiv (Spec.stalkIso Γ(X, U) p).commRingCatIsoToRingEquiv.symm
  have hn : IsIntegrallyClosed (X.presheaf.stalk (hU.fromSpec p)) :=
    IsIntegrallyClosed.of_equiv (asIso (hU.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv.symm
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  rw [hp] at hn
  exact hn

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Normal
