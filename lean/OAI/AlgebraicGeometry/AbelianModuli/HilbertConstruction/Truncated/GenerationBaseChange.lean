import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.ClassificationNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.SingleDegreeGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedGenerationConditions

/-! # Generation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-! The finite single-degree generation conditions survive arbitrary coefficient extension. -/

universe u

variable {R A : CommRingCat.{u}} [Algebra R A] {n B : ℕ} {r : ℕ → ℕ}
variable (D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r)

theorem GradedClassification.TruncatedGradedQuotientData.liftedRelations_baseChange (d : Fin (B + 1)) :
    ((D.baseChange A).quotient d).toSubmodule.map
      (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d A).toLinearMap =
        HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A)
          ((D.quotient d).toSubmodule.map
            (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d R).toLinearMap) := by
  have h := congrArg Module.Grassmannian.toSubmodule (D.baseChangeQuotient_coordinates (A := A) d)
  simpa only [Homogeneous.QuotientClassification.homogeneousLiftedQuotient_relations, HilbertScheme.Presentations.Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap_toSubmodule] using h

theorem GradedClassification.TruncatedGradedQuotientData.generatedFromDegree_baseChange (N : ℕ) (h : D.GeneratedFromDegree N) :
    (D.baseChange A).GeneratedFromDegree N := by
  constructor
  · intro d hd
    apply Submodule.map_injective_of_injective
      (Homogeneous.QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) d A).injective
    rw [Submodule.map_bot, D.liftedRelations_baseChange d, h.1 d hd,
      Submodule.map_bot, Coordinate.GenerationBaseChange.coordinateSubmoduleExtension_bot]
  · intro d hd
    apply (LiftedGenerationConditions.liftedHomogeneous_generation_iff A (Fin (n + 1)) d
      ((D.baseChange A).quotient d.castSucc).toSubmodule
        ((D.baseChange A).quotient d.succ).toSubmodule).mpr
    have hgen := (LiftedGenerationConditions.liftedHomogeneous_generation_iff R (Fin (n + 1)) d
      (D.quotient d.castSucc).toSubmodule (D.quotient d.succ).toSubmodule).mp (h.2 d hd)
    have hs := D.liftedRelations_baseChange (A := A) d.succ
    simp only [Fin.val_succ] at hs
    rw [hs, hgen, Coordinate.GenerationBaseChange.coordinateSubmoduleExtension_iSup]
    apply congrArg iSup
    funext i
    rw [Coordinate.GenerationBaseChange.coordinateSubmoduleExtension_linearImage, LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix_map]
    have ht := D.liftedRelations_baseChange (A := A) d.castSucc
    simp only [Fin.val_castSucc] at ht
    rw [ht]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
