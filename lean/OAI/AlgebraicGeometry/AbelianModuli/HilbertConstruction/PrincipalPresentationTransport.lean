import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.ImmersionPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.BaseChangeComparison

/-! # Principal Presentation Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalPresentationTransport

noncomputable section

/-! Principal presentations transport across commuting ring isomorphisms. -/

universe u v

theorem localizationMap_bijective_of_conjugate
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ψ : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (w : ∀ x, eB (φ x) = ψ (eA x)) (a : A)
    (h : Function.Bijective (IsLocalization.Away.map
      (Localization.Away (eA a)) (Localization.Away (ψ (eA a))) ψ (eA a))) :
    Function.Bijective (IsLocalization.Away.map
      (Localization.Away a) (Localization.Away (φ a)) φ a) := by
  rw [Function.Bijective, IsLocalization.Away.map_injective_iff,
    IsLocalization.Away.map_surjective_iff] at h ⊢
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ := h.1 (eA x) (by rw [← w, hx, map_zero])
    refine ⟨n, eA.injective ?_⟩
    simpa only [map_mul, map_pow, map_zero] using hn
  · intro y
    obtain ⟨x, n, hn⟩ := h.2 (eB y)
    refine ⟨eA.symm x, n, eB.injective ?_⟩
    simpa only [map_mul, map_pow, w, eA.apply_symm_apply] using hn

theorem principal_cover_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    {ι : Type v} (f : ι → A) (h : Ideal.span (Set.range (fun i => e (f i))) = ⊤) :
    Ideal.span (Set.range f) = ⊤ := by
  apply (Ideal.map_eq_top_of_bijective e.toRingHom e.bijective).mp
  rw [Ideal.map_span, ← Set.range_comp]
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalPresentationTransport
