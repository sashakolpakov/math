import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalPrincipalOpenImmersion

/-! # Principal Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalMap

noncomputable section

/-! An equation-based criterion for bijectivity of principal localization maps. -/

open TensorProduct

universe u

def PrincipalMapCriterion {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) : Prop :=
  (∀ x, φ x = 0 → ∃ n : ℕ, a ^ n * x = 0) ∧
  ∀ y, ∃ (x : A) (n : ℕ), φ x = φ a ^ n * y

theorem localizationMap_bijective_iff_criterion
    {A B P Q : Type u} [CommRing A] [CommRing B] [CommRing P] [CommRing Q]
    [Algebra A P] [Algebra B Q] (φ : A →+* B) (a : A)
    [IsLocalization.Away a P] [IsLocalization.Away (φ a) Q] :
    Function.Bijective (IsLocalization.Away.map P Q φ a) ↔ PrincipalMapCriterion φ a := by
  rw [Function.Bijective, IsLocalization.Away.map_injective_iff,
    IsLocalization.Away.map_surjective_iff]
  rfl

theorem principalMapCriterion_of_conjugate
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ψ : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (w : ∀ x, eB (φ x) = ψ (eA x)) (a : A)
    (h : PrincipalMapCriterion ψ (eA a)) : PrincipalMapCriterion φ a := by
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ := h.1 (eA x) (by rw [← w, hx, map_zero])
    refine ⟨n, eA.injective ?_⟩
    simpa only [map_mul, map_pow, map_zero] using hn
  · intro y
    obtain ⟨x, n, hn⟩ := h.2 (eB y)
    refine ⟨eA.symm x, n, eB.injective ?_⟩
    simpa only [map_mul, map_pow, w, eA.apply_symm_apply] using hn

theorem principalBaseChangeMap_bijective_iff_criterion
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B) (a : A) :
    Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R) φ a) ↔
      PrincipalMapCriterion (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom
        ((1 : R) ⊗ₜ[C] a) := by
  have : IsLocalization.Away
      ((Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom ((1 : R) ⊗ₜ[C] a))
      (Localization.Away ((1 : R) ⊗ₜ[C] φ a)) := by
    have heq : (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom ((1 : R) ⊗ₜ[C] a) =
        (1 : R) ⊗ₜ[C] φ a := Algebra.TensorProduct.map_tmul _ _ _ _
    rw [heq]
    infer_instance
  unfold PrincipalLocalizationNaturality.principalBaseChangeMap
  change Function.Bijective (IsLocalization.Away.map _ _ _ _) ↔ _
  exact localizationMap_bijective_iff_criterion _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalMap
