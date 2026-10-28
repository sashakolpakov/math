import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionAffineLocus

/-! # Affine Parameter Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.AffineParameterPoints

noncomputable section

/-! Points of an actual affine quotient parameter scheme on an affine
coefficient test are exactly the ring maps killing its defining ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (R : CommRingCat.{u}) (J : Ideal R)
variable (A : Type u) [CommRing A] [Algebra R A]

theorem quotientRelativeAffineScheme_points_iff :
    Nonempty (Relative.AffinePoints.relativeAffineScheme R A ⟶ Relative.AffinePoints.relativeAffineScheme R (R ⧸ J)) ↔
      J ≤ RingHom.ker (algebraMap R A) := by
  let e := Relative.AffinePoints.relativeAffineGlobalEquiv R A
  have he : Nonempty (Relative.AffinePoints.relativeAffineScheme R A ⟶ Relative.AffinePoints.relativeAffineScheme R (R ⧸ J)) ↔
      Nonempty ((R ⧸ J) →ₐ[R] A) := by
    constructor
    · rintro ⟨f⟩
      exact ⟨e.symm.toAlgHom.comp (Relative.AffinePoints.relativeAffinePointEquiv R (R ⧸ J) (Relative.AffinePoints.relativeAffineScheme R A) f)⟩
    · rintro ⟨f⟩
      exact ⟨(Relative.AffinePoints.relativeAffinePointEquiv R (R ⧸ J) (Relative.AffinePoints.relativeAffineScheme R A)).symm (e.toAlgHom.comp f)⟩
  exact he.trans (Projective.SectionAffineLocus.quotientAlgHom_nonempty_iff J A)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.AffineParameterPoints
