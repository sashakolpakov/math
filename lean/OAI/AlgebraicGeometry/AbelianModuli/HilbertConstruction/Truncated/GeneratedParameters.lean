import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationPointCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ParameterPoints

/-! # Generated Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedParameters

noncomputable section

/-! The concrete open parameter scheme of finite homogeneous quotient data generated from one degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ)

def truncatedGeneratedParameters : Over S :=
  Open.ParameterPoints.openParameterScheme (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S)
    (GenerationOpens.truncatedGeneratedOpen S n B r N)

def truncatedGeneratedInclusion : truncatedGeneratedParameters S n B r N ⟶
    GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S :=
  Open.ParameterPoints.openParameterInclusion _ _

instance truncatedGeneratedInclusion_open :
    IsOpenImmersion (truncatedGeneratedInclusion S n B r N).left :=
  inferInstanceAs (IsOpenImmersion (GenerationOpens.truncatedGeneratedOpen S n B r N).ι)

variable {S n B r N}

theorem truncatedGeneratedPoint_condition {R : CommRingCat.{u}} {f : Spec R ⟶ S}
    (x : Over.mk f ⟶ truncatedGeneratedParameters S n B r N) :
    (GradedRepresentation.truncatedGradedPointData (x ≫ truncatedGeneratedInclusion S n B r N)).GeneratedFromDegree N :=
  (GenerationPointCriterion.truncatedGeneratedOpen_affine_point_iff _ N).mp
    (Open.ParameterPoints.openParameterPointEquiv _ _ (Over.mk f) x).property

theorem truncatedGradedPointData_of_classifyingMap {R : CommRingCat.{u}} (f : Spec R ⟶ S)
    (D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r) :
    GradedRepresentation.truncatedGradedPointData (D.classifyingMap f) = D :=
  GradedClassification.TruncatedGradedQuotientData.classifyingMap_injective f
    (GradedRepresentation.truncatedGradedPointData_classifyingMap (D.classifyingMap f))

def truncatedGeneratedAffinePointEquiv (R : CommRingCat.{u}) (f : Spec R ⟶ S) :
    {D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r // D.GeneratedFromDegree N} ≃
      (Over.mk f ⟶ truncatedGeneratedParameters S n B r N) :=
  (Equiv.subtypeEquiv (GradedRepresentation.truncatedGradedAffinePointEquiv.{u, 0} R f) (by
    intro D
    change D.GeneratedFromDegree N ↔
      Set.range (D.classifyingMap f).left ⊆ (GenerationOpens.truncatedGeneratedOpen S n B r N : Set _)
    rw [GenerationPointCriterion.truncatedGeneratedOpen_affine_point_iff, truncatedGradedPointData_of_classifyingMap])).trans
      (Open.ParameterPoints.openParameterPointEquiv _ _ (Over.mk f)).symm

theorem truncatedGeneratedAffinePointEquiv_inclusion (R : CommRingCat.{u}) (f : Spec R ⟶ S)
    (D : {D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r // D.GeneratedFromDegree N}) :
    truncatedGeneratedAffinePointEquiv R f D ≫ truncatedGeneratedInclusion S n B r N =
      D.val.classifyingMap f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (GenerationOpens.truncatedGeneratedOpen S n B r N).ι
    (D.val.classifyingMap f).left _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedParameters
