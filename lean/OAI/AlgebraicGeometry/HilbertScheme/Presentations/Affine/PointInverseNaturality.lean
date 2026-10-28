import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Point Inverse Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.PointInverseNaturality

noncomputable section

/-! Inverting affine point coordinates commutes with algebra-map postcomposition. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
theorem relativeAffinePointEquiv_symm_postcomp
    (R : CommRingCat.{u}) (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (T : Over (Spec R)) (φ : A →ₐ[R] B)
    (ρ : B →ₐ[R] Relative.AffinePoints.relativeGlobalAlgebra R T) :
    (Relative.AffinePoints.relativeAffinePointEquiv R B T).symm ρ ≫ (algSpec R).map (CommAlgCat.ofHom φ).op =
      (Relative.AffinePoints.relativeAffinePointEquiv R A T).symm (ρ.comp φ) := by
  apply (Relative.AffinePoints.relativeAffinePointEquiv R A T).injective
  rw [Relative.AffinePoints.relativeAffinePointEquiv_postcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.PointInverseNaturality
