import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.AffineParameterPoints

/-! # Spectrum Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.SpectrumFactorization

noncomputable section

/-! The actual spectrum of a quotient represents unique affine
factorization through the closed subscheme defined by its ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : CommRingCat.{u}) (J : Ideal R)

def quotientSpecInclusion : Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

instance quotientSpecInclusion_isClosedImmersion : IsClosedImmersion (quotientSpecInclusion R J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem quotientSpec_lift_iff (A : Type u) [CommRing A] (φ : R →+* A) :
    (∃ g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (R ⧸ J)),
      g ≫ quotientSpecInclusion R J = Spec.map (CommRingCat.ofHom φ)) ↔ J ≤ RingHom.ker φ := by
  let : Algebra R A := φ.toAlgebra
  have he : (∃ g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (R ⧸ J)),
      g ≫ quotientSpecInclusion R J = Spec.map (CommRingCat.ofHom φ)) ↔
      Nonempty (Relative.AffinePoints.relativeAffineScheme R A ⟶ Relative.AffinePoints.relativeAffineScheme R (R ⧸ J)) := by
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨Over.homMk g hg⟩
    · rintro ⟨g⟩
      exact ⟨g.left, g.w⟩
  exact he.trans (AffineParameterPoints.quotientRelativeAffineScheme_points_iff R J A)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.SpectrumFactorization
