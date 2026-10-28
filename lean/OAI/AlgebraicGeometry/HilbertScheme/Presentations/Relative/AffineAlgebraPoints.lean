import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Affine Algebra Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineAlgebraPoints

noncomputable section

/-! Algebra-valued points of an affine spectrum, before specializing its coefficient rings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R : CommRingCat.{u}) (C : Type u) [CommRing C] [Algebra R C]
variable (A : Type u) [CommRing A] [Algebra R A]

def relativeAffineAlgebraPoint
    (x : AffinePoints.relativeAffineScheme R C ⟶ AffinePoints.relativeAffineScheme R A) : A →ₐ[R] C :=
  (AffinePoints.relativeAffineGlobalEquiv R C).symm.toAlgHom.comp (AffinePoints.relativeAffinePointEquiv R A _ x)

theorem relativeAffineAlgebraPoint_postcomp
    {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (x : AffinePoints.relativeAffineScheme R C ⟶ AffinePoints.relativeAffineScheme R B) :
    relativeAffineAlgebraPoint R C A (x ≫ (algSpec R).map (CommAlgCat.ofHom φ).op) =
      (relativeAffineAlgebraPoint R C B x).comp φ := by
  ext a
  exact congrArg (fun ρ => (AffinePoints.relativeAffineGlobalEquiv R C).symm (ρ a))
    (AffinePoints.relativeAffinePointEquiv_postcomp R A φ x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineAlgebraPoints
