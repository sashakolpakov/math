import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.ClassificationNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IdealBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality

/-! # Affine Universal Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.AffineUniversalData

noncomputable section

/-! The actual finite quotient data and generated ideal attached to every affine parameter point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B : ℕ} {r : ℕ → ℕ}
variable {R A : CommRingCat.{u}}

def truncatedAffineUniversalData
    (x : Spec R ⟶ (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left) :
    GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r :=
  GradedRepresentation.truncatedGradedPointData (Over.homMk x rfl :
    Over.mk (x ≫ (GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).hom) ⟶
      GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S)

theorem truncatedAffineUniversalData_classifyingMap
    (x : Spec R ⟶ (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left) :
    (truncatedAffineUniversalData x).classifyingMap
      (x ≫ (GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).hom) = Over.homMk x rfl :=
  GradedRepresentation.truncatedGradedPointData_classifyingMap _

theorem truncatedAffineUniversalData_naturality (φ : R ⟶ A)
    (x : Spec R ⟶ (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left) :
    letI : Algebra R A := φ.hom.toAlgebra
    truncatedAffineUniversalData (Spec.map φ ≫ x) = (truncatedAffineUniversalData x).baseChange A := by
  let : Algebra R A := φ.hom.toAlgebra
  let M := GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S
  let D := truncatedAffineUniversalData x
  apply GradedClassification.TruncatedGradedQuotientData.classifyingMap_injective (Spec.map φ ≫ (x ≫ M.hom))
  change (truncatedAffineUniversalData (Spec.map φ ≫ x)).classifyingMap
    (Spec.map φ ≫ (x ≫ M.hom)) =
      (D.baseChange A).classifyingMap (Spec.map φ ≫ (x ≫ M.hom))
  have hleft : (truncatedAffineUniversalData (Spec.map φ ≫ x)).classifyingMap
      (Spec.map φ ≫ (x ≫ M.hom)) = Over.homMk (Spec.map φ ≫ x) (Category.assoc _ _ _) := by
    apply Over.OverMorphism.ext
    exact congrArg (fun k => k.left) (truncatedAffineUniversalData_classifyingMap (Spec.map φ ≫ x))
  have hright : (D.baseChange A).classifyingMap (Spec.map φ ≫ (x ≫ M.hom)) =
      (Over.homMk (Spec.map φ) rfl : Over.mk (Spec.map φ ≫ (x ≫ M.hom)) ⟶
        Over.mk (x ≫ M.hom)) ≫ D.classifyingMap (x ≫ M.hom) :=
    D.classifyingMap_natural (A := A) (x ≫ M.hom)
  rw [hleft, hright]
  have hx : D.classifyingMap (x ≫ M.hom) = Over.homMk x rfl :=
    truncatedAffineUniversalData_classifyingMap x
  rw [hx]
  apply Over.OverMorphism.ext
  rfl

def truncatedAffineUniversalIdeal
    (x : Spec R ⟶ (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left) :
    (Projective.ProjectivePresentations.affineProjectiveSpace R n).left.IdealSheafData :=
  (truncatedAffineUniversalData x).projectiveIdeal

theorem truncatedAffineUniversalIdeal_naturality (φ : R ⟶ A)
    (x : Spec R ⟶ (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left) :
    truncatedAffineUniversalIdeal (Spec.map φ ≫ x) =
      (truncatedAffineUniversalIdeal x).comap (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) := by
  let : Algebra R A := φ.hom.toAlgebra
  change (truncatedAffineUniversalData (Spec.map φ ≫ x)).projectiveIdeal = _
  rw [truncatedAffineUniversalData_naturality φ x]
  exact (truncatedAffineUniversalData x).projectiveIdeal_baseChange

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.AffineUniversalData
