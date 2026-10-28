import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.ClassifierRecovery

/-! # Point Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointEquivalence

noncomputable section

/-! The constructed combined parameter classifies exactly the complete bounded moduli isomorphisms on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
variable (PD : Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme) (PE : Projective.ProjectivePresentations.ProjectivePresentation B.dual.abelian.scheme)

def boundedPolarizedLevelIsoPointEquiv (T : Over S) :
    (T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P) ≃ IsomorphismFunctor.BoundedFamilyLevelIso A B j P T where
  toFun := (ClassifyingMap.boundedPolarizedLevelClassifyingMap A B j P PB PD PE).app (.op T)
  invFun := IsomorphismFunctor.BoundedFamilyLevelIso.classifier A B j P PB
  right_inv := ClassifierRecovery.boundedPolarizedLevelClassifyingMap_recovers A B j P PB PD PE
  left_inv c := by
    have := ClassifyingMap.boundedPolarizedLevelClassifyingMap_mono A B j P PB PD PE
    apply CategoryTheory.injective_of_mono
      ((ClassifyingMap.boundedPolarizedLevelClassifyingMap A B j P PB PD PE).app (.op T))
    exact ClassifierRecovery.boundedPolarizedLevelClassifyingMap_recovers A B j P PB PD PE
      ((ClassifyingMap.boundedPolarizedLevelClassifyingMap A B j P PB PD PE).app (.op T) c)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.PointEquivalence
