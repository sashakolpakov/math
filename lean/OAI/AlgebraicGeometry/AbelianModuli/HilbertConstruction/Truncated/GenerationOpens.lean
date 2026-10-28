import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.GenerationLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroRelationLocus
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.IncidenceEquivalence

/-! # Generation Opens -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationOpens

noncomputable section

/-! Actual open conditions for single-degree generation on the finite graded quotient parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ)

theorem truncatedGradedProjection_incidence (d : Fin B) (i : Fin (n + 1)) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition
      (GradedParameters.truncatedGradedProjection.{u, 0} (Fin (n + 1)) B r S d.castSucc)
      (GradedParameters.truncatedGradedProjection.{u, 0} (Fin (n + 1)) B r S d.succ)
      (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, 0}
        Γ((GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left, ⊤) (Fin (n + 1)) d i)
      (𝟙 (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S)) := by
  let M := GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S
  let j := GradedParameters.truncatedGradedInclusion.{u, 0} (Fin (n + 1)) B r S
  let q := QuotientParameters.truncatedQuotientProjection.{u, 0} (Fin (n + 1)) B r S d.castSucc
  let k := QuotientParameters.truncatedQuotientProjection.{u, 0} (Fin (n + 1)) B r S d.succ
  let F := LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, 0}
    Γ((QuotientParameters.truncatedQuotientParameters.{u, 0} (Fin (n + 1)) B r S).left, ⊤) (Fin (n + 1)) d i
  have h : Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k F (𝟙 M ≫ j) :=
    (((Closed.ConditionIntersections.closedConditionIntersectionModel
      (GradedParameters.truncatedMultiplicationSubfunctor.{u, 0} (Fin (n + 1)) B r S)
      (GradedParameters.truncatedMultiplicationClosedModel (Fin (n + 1)) B r S)).pointMap.app (.op M)) (𝟙 M)).property ⟨d, i⟩
  rw [Category.id_comp] at h
  have hp := (Affine.IncidenceEquivalence.grassmannIncidenceCondition_pullback q k F j).mp h
  change Grassmann.IncidenceCondition.GrassmannIncidenceCondition (j ≫ q) (j ≫ k)
    ((LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, 0}
      Γ((QuotientParameters.truncatedQuotientParameters.{u, 0} (Fin (n + 1)) B r S).left, ⊤) (Fin (n + 1)) d i).map
        j.left.appTop.hom) (𝟙 M) at hp
  rw [LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix_map] at hp
  exact hp

def truncatedDegreeGenerationOpen (d : Fin B) :
    (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left.Opens :=
  Homogeneous.GenerationLocus.homogeneousGenerationOpen.{u, 0} (Fin (n + 1)) d (r d) (r d.succ)
    (GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S d.castSucc)
    (GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S d.succ)
    (truncatedGradedProjection_incidence S n B r d)

def truncatedDegreeZeroRelationOpen (d : Fin (B + 1)) :
    (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left.Opens :=
  ZeroRelationLocus.homogeneousZeroRelationOpen.{u, 0} (Fin (n + 1)) d (r d)
    (GradedParameters.truncatedGradedProjection (Fin (n + 1)) B r S d)

def truncatedGeneratedOpen (N : ℕ) :
    (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left.Opens :=
  (⨅ d : Fin (B + 1), if d.val < N then truncatedDegreeZeroRelationOpen S n B r d else ⊤) ⊓
    (⨅ d : Fin B, if N ≤ d.val then truncatedDegreeGenerationOpen S n B r d else ⊤)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationOpens
