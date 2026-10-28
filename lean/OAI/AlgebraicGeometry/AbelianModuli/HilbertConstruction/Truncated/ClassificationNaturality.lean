import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.RelationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.QuotientBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterNaturality

/-! # Classification Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-!
The affine representation of finite compatible quotient tuples is natural
under arbitrary coefficient extension, with the actual tensor-product
quotients on the algebraic side and precomposition on the scheme side.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : CommRingCat.{u}} [Algebra R A] {n B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r)

theorem GradedClassification.TruncatedGradedQuotientData.baseChangeQuotient_coordinates (d : Fin (B + 1)) :
    Homogeneous.QuotientClassification.homogeneousLiftedQuotient.{u, 0} (Fin (n + 1)) d (r d) A ((D.baseChange A).quotient d) =
      HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap (algebraMap R A)
        (Homogeneous.QuotientClassification.homogeneousLiftedQuotient.{u, 0} (Fin (n + 1)) d (r d) R (D.quotient d)) := by
  apply Module.Grassmannian.ext
  rw [Homogeneous.QuotientClassification.homogeneousLiftedQuotient_relations, HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap_toSubmodule,
    Homogeneous.QuotientClassification.homogeneousLiftedQuotient_relations]
  have h := Homogeneous.RelationBaseChange.homogeneousLiftedRelations_baseChange (A := A) D.generatedIdeal d
  change (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) D.generatedIdeal).toIdeal d).map
    (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d A).toLinearMap = _
  refine h.trans ?_
  change HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A)
    ((Homogeneous.IdealIncidence.homogeneousDegreeRelations D.generatedIdeal d).map
      (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d R).toLinearMap) = _
  rw [D.generatedIdeal_degree]

variable {S : Scheme.{u}} (f : Spec R ⟶ S)

theorem GradedClassification.TruncatedGradedQuotientData.degree_classifying_natural (d : Fin (B + 1)) :
    Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) d (r d) A
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ f) ((D.baseChange A).quotient d) =
        (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ f) ⟶ Over.mk f) ≫
            Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) d (r d) R f (D.quotient d) := by
  rw [Homogeneous.QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates,
    Homogeneous.QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates, D.baseChangeQuotient_coordinates]
  exact Grassmann.ParameterNaturality.grassmannParameter_classifying_naturality R A (algebraMap R A) f _

theorem GradedClassification.TruncatedGradedQuotientData.classifyingMap_natural :
    (D.baseChange A).classifyingMap (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ f) =
      (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ f) ⟶ Over.mk f) ≫
          D.classifyingMap f := by
  let x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ f) ⟶ Over.mk f :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) rfl
  symm
  apply ((D.baseChange A).existsUnique_classifyingMap
    (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ f)).choose_spec.2 (x ≫ D.classifyingMap f)
  intro d
  rw [Category.assoc, D.classifyingMap_projection]
  exact (D.degree_classifying_natural f d).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
