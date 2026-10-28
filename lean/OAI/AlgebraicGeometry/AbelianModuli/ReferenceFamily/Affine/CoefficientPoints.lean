import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Point

/-! # Coefficient Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientPoints

noncomputable section

/-! Every coefficient homomorphism into a ring determines an actual
point of an affine scheme, with exactly the prescribed coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (X : Scheme.{u}) [IsAffine X] {C : Type u} [CommRing C]
  (φ : Γ(X, ⊤) →+* C)

def affineCoefficientPoint : Spec (.of C) ⟶ X :=
  Spec.map (CommRingCat.ofHom φ) ≫ inv X.toSpecΓ

theorem affineCoefficientPoint_coefficients :
    HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (affineCoefficientPoint X φ) = φ := by
  have h : CommRingCat.ofHom (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (affineCoefficientPoint X φ)) =
      CommRingCat.ofHom φ := by
    apply Spec.map_injective
    rw [HilbertScheme.Presentations.Projective.Point.schemePointCoefficientMap_spec]
    change (Spec.map (CommRingCat.ofHom φ) ≫ inv X.toSpecΓ) ≫ X.toSpecΓ = _
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact congrArg CommRingCat.Hom.hom h

omit [IsAffine X] in
theorem schemePointCoefficientMap_preimage (q : Spec (.of C) ⟶ X) :
    (Spec.preimage (q ≫ X.toSpecΓ)).hom = HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q := by
  have h : Spec.preimage (q ≫ X.toSpecΓ) =
      CommRingCat.ofHom (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q) := by
    apply Spec.map_injective
    rw [Spec.map_preimage, HilbertScheme.Presentations.Projective.Point.schemePointCoefficientMap_spec]
  exact congrArg CommRingCat.Hom.hom h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientPoints
