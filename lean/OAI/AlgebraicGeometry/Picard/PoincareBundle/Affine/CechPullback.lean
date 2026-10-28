import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Cech Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechPullback

noncomputable section

/-!
# The affine tensor overlap is the actual scheme-theoretic kernel pair
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct
open scoped TensorProduct

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Actual scheme-theoretic overlap, including all nonreduced structure. -/
def overlapIso :
    letI := f.hom.toAlgebra
    pullback (Spec.map f) (Spec.map f) ≅ Spec (CommRingCat.of (S ⊗[R] S)) := by
  letI := f.hom.toAlgebra
  exact pullbackSpecIso R S S

theorem overlapIso_inv_fst :
    letI := f.hom.toAlgebra
    (overlapIso f).inv ≫ pullback.fst (Spec.map f) (Spec.map f) = Spec.map (CechCanonicalCoordinates.firstProjection f) := by
  let := f.hom.toAlgebra
  exact pullbackSpecIso_inv_fst' R S S

theorem overlapIso_inv_snd :
    letI := f.hom.toAlgebra
    (overlapIso f).inv ≫ pullback.snd (Spec.map f) (Spec.map f) = Spec.map (CechCanonicalCoordinates.secondProjection f) := by
  let := f.hom.toAlgebra
  exact pullbackSpecIso_inv_snd R S S

theorem overlapIso_hom_fst :
    letI := f.hom.toAlgebra
    (overlapIso f).hom ≫ Spec.map (CechCanonicalCoordinates.firstProjection f) = pullback.fst (Spec.map f) (Spec.map f) := by
  let := f.hom.toAlgebra
  exact pullbackSpecIso_hom_fst' R S S

theorem overlapIso_hom_snd :
    letI := f.hom.toAlgebra
    (overlapIso f).hom ≫ Spec.map (CechCanonicalCoordinates.secondProjection f) = pullback.snd (Spec.map f) (Spec.map f) := by
  let := f.hom.toAlgebra
  exact pullbackSpecIso_hom_snd R S S

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechPullback
