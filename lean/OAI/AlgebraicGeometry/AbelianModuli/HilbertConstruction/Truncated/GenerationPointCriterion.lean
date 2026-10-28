import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationOpens
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.SingleDegreeGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.OpenConditions

/-! # Generation Point Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationPointCriterion

noncomputable section

/-! Affine points of the concrete open locus are exactly finite quotient data generated from the specified degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B : ℕ} {r : ℕ → ℕ} {R : CommRingCat.{u}} {f : Spec R ⟶ S}
variable (x : Over.mk f ⟶ GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S)

theorem truncatedDegreeGenerationOpen_point_iff (d : Fin B) :
    Set.range x.left ⊆ (GenerationOpens.truncatedDegreeGenerationOpen S n B r d : Set _) ↔
      ((GradedRepresentation.truncatedGradedPointData x).quotient d.succ).toSubmodule =
        ⨆ i : Fin (n + 1), ((GradedRepresentation.truncatedGradedPointData x).quotient d.castSucc).toSubmodule.map
          (Homogeneous.MultiplicationMatrices.homogeneousMultiplyX R (Fin (n + 1)) d i) :=
  Homogeneous.GenerationLocus.homogeneousGenerationOpen_affine_point_iff (Fin (n + 1)) d (r d) (r d.succ) _ _
    (GenerationOpens.truncatedGradedProjection_incidence S n B r d) R f x
    ((GradedRepresentation.truncatedGradedPointData x).quotient d.castSucc) ((GradedRepresentation.truncatedGradedPointData x).quotient d.succ)
    (GradedRepresentation.truncatedGradedPointQuotient_projection x d.castSucc) (GradedRepresentation.truncatedGradedPointQuotient_projection x d.succ)

theorem truncatedDegreeZeroRelationOpen_point_iff (d : Fin (B + 1)) :
    Set.range x.left ⊆ (GenerationOpens.truncatedDegreeZeroRelationOpen S n B r d : Set _) ↔
      ((GradedRepresentation.truncatedGradedPointData x).quotient d).toSubmodule = ⊥ :=
  ZeroRelationLocus.homogeneousZeroRelationOpen_affine_point_iff (Fin (n + 1)) d (r d) _ R f x
    ((GradedRepresentation.truncatedGradedPointData x).quotient d) (GradedRepresentation.truncatedGradedPointQuotient_projection x d)

theorem truncatedGeneratedOpen_affine_point_iff (N : ℕ) :
    Set.range x.left ⊆ (GenerationOpens.truncatedGeneratedOpen S n B r N : Set _) ↔
      (GradedRepresentation.truncatedGradedPointData x).GeneratedFromDegree N := by
  rw [GenerationOpens.truncatedGeneratedOpen, TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff,
    Finite.OpenConditions.range_subset_finite_conditional_opens, Finite.OpenConditions.range_subset_finite_conditional_opens]
  constructor
  · intro h
    exact ⟨fun d hd => (truncatedDegreeZeroRelationOpen_point_iff x d).mp (h.1 d hd),
      fun d hd => (truncatedDegreeGenerationOpen_point_iff x d).mp (h.2 d hd)⟩
  · intro h
    exact ⟨fun d hd => (truncatedDegreeZeroRelationOpen_point_iff x d).mpr (h.1 d hd),
      fun d hd => (truncatedDegreeGenerationOpen_point_iff x d).mpr (h.2 d hd)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationPointCriterion
