import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ClassifyingMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.InverseClassifier

/-! # Classifier Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ClassifierRecovery

noncomputable section

/-! Classifying and then specializing the universal isomorphism recovers every bounded complete moduli isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem boundedPolarizedLevelClassifyingMap_recovers_abelian
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)
    {T : Over S} (e : IsomorphismFunctor.BoundedFamilyLevelIso A B j P T) :
    ((ClassifyingMap.boundedPolarizedLevelClassifyingMap A B j P PB PD PE).app (.op T)
      (IsomorphismFunctor.BoundedFamilyLevelIso.classifier A B j P PB e)).val.abelian.hom = e.val.abelian.hom := by
  have h := ClassifyingMap.boundedPolarizedLevelClassifyingMap_abelian A B j P PB PD PE
    (IsomorphismFunctor.BoundedFamilyLevelIso.classifier A B j P PB e)
  rw [IsomorphismFunctor.BoundedFamilyLevelIso.classifier_comp, IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier_point] at h
  exact h

theorem boundedPolarizedLevelClassifyingMap_recovers
    {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
    (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)
    {T : Over S} (e : IsomorphismFunctor.BoundedFamilyLevelIso A B j P T) :
    (ClassifyingMap.boundedPolarizedLevelClassifyingMap A B j P PB PD PE).app (.op T)
      (IsomorphismFunctor.BoundedFamilyLevelIso.classifier A B j P PB e) = e :=
  Subtype.ext (Moduli.Isomorphisms.LevelPreservingIso.ext_abelian _ _
    (boundedPolarizedLevelClassifyingMap_recovers_abelian A B j P PB PD PE e))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ClassifierRecovery
