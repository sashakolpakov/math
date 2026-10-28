import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalPrincipalMapDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ImmersionPrincipalCriterion

/-! # Natural Principal Open Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalPrincipalOpenImmersion

noncomputable section

/-! The natural base change is an open immersion when its localized maps are bijective and cover. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem principalBaseChangeMap_bijective_canonical (φ : A →ₐ[C] B) (a : A) :
    Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R) φ a) ↔
      Function.Bijective (IsLocalization.Away.map
        (Localization.Away ((1 : R) ⊗ₜ[C] a))
        (Localization.Away (Algebra.TensorProduct.map (AlgHom.id R R) φ ((1 : R) ⊗ₜ[C] a)))
        (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom ((1 : R) ⊗ₜ[C] a)) := by
  have : IsLocalization.Away
      ((Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom ((1 : R) ⊗ₜ[C] a))
      (Localization.Away ((1 : R) ⊗ₜ[C] φ a)) := by
    have heq : (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom ((1 : R) ⊗ₜ[C] a) =
        (1 : R) ⊗ₜ[C] φ a := Algebra.TensorProduct.map_tmul _ _ _ _
    rw [heq]
    infer_instance
  unfold PrincipalLocalizationNaturality.principalBaseChangeMap
  change Function.Bijective (IsLocalization.Away.map _ _ _ _) ↔ _
  rw [Function.Bijective, Function.Bijective,
    IsLocalization.Away.map_injective_iff, IsLocalization.Away.map_surjective_iff,
    IsLocalization.Away.map_injective_iff, IsLocalization.Away.map_surjective_iff]

theorem natural_tensorMap_isOpenImmersion_of_principal_cover
    (φ : A →ₐ[C] B) {ι : Type v} (f : ι → A)
    (hcover : Ideal.span (Set.range (fun i => (1 : R) ⊗ₜ[C] φ (f i))) = ⊤)
    (hiso : ∀ i, Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R) φ (f i))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom)) := by
  apply AffineOpen.ImmersionPrincipalCriterion.isOpenImmersion_SpecMap_of_principal_isomorphisms _ (fun i => (1 : R) ⊗ₜ[C] f i)
  · simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply] using hcover
  · intro i
    exact (principalBaseChangeMap_bijective_canonical φ (f i)).mp (hiso i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalPrincipalOpenImmersion
