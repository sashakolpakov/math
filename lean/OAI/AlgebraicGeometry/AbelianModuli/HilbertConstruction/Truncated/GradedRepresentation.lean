import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.IncidenceEquivalence

/-! # Graded Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedRepresentation

noncomputable section

/-!
Affine points of the actual truncated graded parameter scheme are exactly
finite tuples of actual fixed-rank homogeneous quotients whose relation
modules satisfy variable multiplication in every retained degree.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {σ : Type v} [Finite σ] {B : ℕ} {r : ℕ → ℕ}
variable {R : CommRingCat.{max u v}} {S : Scheme.{max u v}} {f : Spec R ⟶ S}
variable (g : Over.mk f ⟶ GradedParameters.truncatedGradedParameters.{u, v} σ B r S)

def truncatedGradedPointQuotient (d : Fin (B + 1)) :
    Module.Grassmannian R (MvPolynomial.homogeneousSubmodule σ R d) (r d) :=
  (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) R f).symm
    (g ≫ GradedParameters.truncatedGradedProjection σ B r S d)

theorem truncatedGradedPointQuotient_projection (d : Fin (B + 1)) :
    g ≫ GradedParameters.truncatedGradedProjection σ B r S d =
      Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) R f
        (truncatedGradedPointQuotient g d) :=
  ((Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, v} σ d (r d) R f).apply_symm_apply _).symm

theorem truncatedGradedPoint_condition (a : Fin B × σ) :
    g ≫ GradedParameters.truncatedGradedInclusion σ B r S ∈
      (GradedParameters.truncatedMultiplicationSubfunctor.{u, v} σ B r S a).obj (.op (Over.mk f)) :=
  (((Closed.ConditionIntersections.closedConditionIntersectionModel
    (GradedParameters.truncatedMultiplicationSubfunctor.{u, v} σ B r S)
    (GradedParameters.truncatedMultiplicationClosedModel σ B r S)).pointMap.app (.op (Over.mk f))) g).property a

def truncatedGradedPointData : GradedClassification.TruncatedGradedQuotientData R σ B r where
  quotient := truncatedGradedPointQuotient g
  variable_mul d i := by
    apply (Homogeneous.IncidenceEquivalence.homogeneousIncidenceCondition_affine_iff σ d (r d) (r d.succ)
      (QuotientParameters.truncatedQuotientProjection σ B r S d.castSucc)
      (QuotientParameters.truncatedQuotientProjection σ B r S d.succ) R f
      (g ≫ GradedParameters.truncatedGradedInclusion σ B r S)
      (truncatedGradedPointQuotient g d.castSucc) (truncatedGradedPointQuotient g d.succ)
      ((Category.assoc _ _ _).trans (truncatedGradedPointQuotient_projection g d.castSucc))
      ((Category.assoc _ _ _).trans (truncatedGradedPointQuotient_projection g d.succ)) i).mp
    exact truncatedGradedPoint_condition g ⟨d, i⟩

theorem truncatedGradedPointData_classifyingMap :
    (truncatedGradedPointData g).classifyingMap f = g :=
  ((truncatedGradedPointData g).existsUnique_classifyingMap f).choose_spec.2 g
    (truncatedGradedPointQuotient_projection g) |>.symm

def truncatedGradedAffinePointEquiv (R : CommRingCat.{max u v}) (f : Spec R ⟶ S) :
    GradedClassification.TruncatedGradedQuotientData R σ B r ≃
      (Over.mk f ⟶ GradedParameters.truncatedGradedParameters.{u, v} σ B r S) :=
  Equiv.ofBijective (fun D => D.classifyingMap f)
    ⟨GradedClassification.TruncatedGradedQuotientData.classifyingMap_injective f,
      fun g => ⟨truncatedGradedPointData g, truncatedGradedPointData_classifyingMap g⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedRepresentation
