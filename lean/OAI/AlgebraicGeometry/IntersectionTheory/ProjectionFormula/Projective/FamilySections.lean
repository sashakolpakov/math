import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ProjectiveProper

/-! # Family Sections -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySections

noncomputable section

/-! Every good marked parameter gives a closed projective slice.
The source model is proper over the actual parameter scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

theorem ambient_closed {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)
    (t : ℂ) (ht : (Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    IsClosedImmersion (MatrixFamily.Family.specialization A t ht) := by
  let : IsClosedImmersion (MatrixFamily.Family.specialization A t ht ≫
      FamilySupport.Family.projection A) := by
    rw [FamilySupport.Family.specialization_projection]
    infer_instance
  exact IsClosedImmersion.of_comp _ (FamilySupport.Family.projection A)

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

instance toAmbient_closed : IsClosedImmersion (FamilyOnSource.Family.toAmbient X A) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst (FamilySupport.Family.projection A) X.embedding))

theorem source_closed (t : ℂ) (ht : (Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    IsClosedImmersion (FamilyOnSource.Family.specialization X A t ht) := by
  let : IsSeparated (FamilyOnSource.Family.toSource X A) :=
    inferInstanceAs (IsSeparated (pullback.snd (FamilySupport.Family.projection A) X.embedding))
  let : IsClosedImmersion (FamilyOnSource.Family.specialization X A t ht ≫
      FamilyOnSource.Family.toSource X A) := by
    rw [FamilyOnSource.Family.specialization_source]
    infer_instance
  exact IsClosedImmersion.of_comp _ (FamilyOnSource.Family.toSource X A)

def parameter : FamilyOnSource.Family.space X A ⟶ Spec (.of (Polynomial.MatrixPath.Ring A)) :=
  FamilyOnSource.Family.toAmbient X A ≫ Relative.ProjectiveI.Base.base (Polynomial.MatrixPath.Ring A) X.ambientDimension

instance proper_parameter : IsProper (parameter X A) := by
  unfold parameter
  infer_instance

instance noetherian : IsNoetherian (FamilyOnSource.Family.space X A) where

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySections
