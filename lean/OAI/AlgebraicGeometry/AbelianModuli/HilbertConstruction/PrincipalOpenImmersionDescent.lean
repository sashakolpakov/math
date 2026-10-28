import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalPrincipalOpenImmersion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalCoverExtension

/-! # Principal Open Immersion Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalOpenImmersionDescent

noncomputable section

/-! Finite principal presentations of open immersions descend to finite coefficients. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem exists_principal_openImmersion_descent
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B]
    [Algebra.FiniteType C A] [Algebra.FiniteType C B]
    [Module.Flat C A] [Module.Flat C B]
    (φ : A →ₐ[C] B) {ι : Type v} [Finite ι] (f : ι → A)
    (hcover : Ideal.span (Set.range (fun i => (1 : R) ⊗ₜ[C] φ (f i))) = ⊤)
    (hiso : ∀ i, Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R) φ (f i)))
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      Ideal.span (Set.range (fun i => (1 : D) ⊗ₜ[C] φ (f i))) = ⊤ ∧
      (∀ i, Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := D) φ (f i))) ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id D D) φ).toRingHom)) := by
  obtain ⟨F, hEF, hF, hcoverF⟩ := HilbertConstruction.Flat.PrincipalCoverDescent.exists_flat_principal_cover_descent
    (fun i => φ (f i)) hcover E hE
  obtain ⟨D, hFD, hD, hisoD⟩ := NaturalPrincipalMapDescent.exists_common_natural_principalMap_bijective φ f hiso F hF
  have hcoverD := PrincipalCoverExtension.principal_cover_coefficient_mono hFD (fun i => φ (f i)) hcoverF
  exact ⟨D, hEF.trans hFD, hD, hcoverD, hisoD,
    NaturalPrincipalOpenImmersion.natural_tensorMap_isOpenImmersion_of_principal_cover φ f hcoverD hisoD⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalOpenImmersionDescent
