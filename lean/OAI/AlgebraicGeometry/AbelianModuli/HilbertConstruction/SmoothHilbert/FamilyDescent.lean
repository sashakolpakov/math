import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.FamilyDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ProjectiveFamilyDescent

/-! # Family Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smooth Hilbert families over arbitrary rings descend to noetherian smooth Hilbert families in the same projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Flat.ClosedFamilies.FlatClosedHilbertFamily.exists_smooth_noetherian_hilbert_family
    {R : Type u} [CommRing R] {n : ℕ} {P : Polynomial ℚ}
    (F : Flat.ClosedFamilies.FlatClosedHilbertFamily R n P) [Smooth F.val.scheme.hom] :
    ∃ K : Subalgebra ℤ R, Algebra.FiniteType ℤ K ∧ IsNoetherianRing K ∧
      ∃ G : Flat.ClosedFamilies.FlatClosedHilbertFamily K n P, Smooth G.val.scheme.hom ∧
        F.val = G.val.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap (CommRingCat.ofHom K.val.toRingHom) n)
          (Spec.map (CommRingCat.ofHom K.val.toRingHom))
          (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (CommRingCat.ofHom K.val.toRingHom) n) := by
  obtain ⟨K, hK, hN, G, hG, he⟩ := F.val.exists_smooth_noetherian_projective_family
  have : IsNoetherianRing K := hN
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := CommRingCat.ofHom K.val.toRingHom
  have hP := G.hilbert_of_injective_coefficient_recovery φ Subtype.val_injective F he
  exact ⟨K, hK, hN, ⟨G, hP⟩, hG, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
