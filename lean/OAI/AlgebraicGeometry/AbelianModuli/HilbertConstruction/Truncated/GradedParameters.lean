import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.QuotientParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationLocus

/-! # Graded Parameters -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedParameters

noncomputable section

/-!
An actual closed parameter scheme for finite tuples of homogeneous quotients
satisfying the variable-multiplication incidences in every retained degree.
Its universal property keeps the degree projections explicit.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

variable (σ : Type v) [Finite σ] (B : ℕ) (r : ℕ → ℕ) (S : Scheme.{max u v})

def truncatedMultiplicationSubfunctor (a : Fin B × σ) :
    Subfunctor (yoneda.obj (QuotientParameters.truncatedQuotientParameters.{u, v} σ B r S)) :=
  Grassmann.IncidenceUniversality.grassmannIncidenceSubfunctor
    (QuotientParameters.truncatedQuotientProjection σ B r S a.1.castSucc)
    (QuotientParameters.truncatedQuotientProjection σ B r S a.1.succ)
    (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v}
      Γ((QuotientParameters.truncatedQuotientParameters.{u, v} σ B r S).left, ⊤) σ a.1 a.2)

def truncatedMultiplicationClosedModel (a : Fin B × σ) :
    Closed.ConditionIdeals.ClosedConditionModel (truncatedMultiplicationSubfunctor.{u, v} σ B r S a) :=
  Grassmann.IncidenceUniversality.grassmannIncidenceClosedModel _ _ _

def truncatedGradedParameters : Over S :=
  Closed.ConditionIntersections.closedConditionIntersectionScheme (truncatedMultiplicationSubfunctor.{u, v} σ B r S)
    (truncatedMultiplicationClosedModel σ B r S)

def truncatedGradedInclusion : truncatedGradedParameters.{u, v} σ B r S ⟶
    QuotientParameters.truncatedQuotientParameters.{u, v} σ B r S :=
  Closed.ConditionIntersections.closedConditionIntersectionInclusion _ _

instance truncatedGradedInclusion_closed :
    IsClosedImmersion (truncatedGradedInclusion.{u, v} σ B r S).left :=
  Closed.ConditionIntersections.closedConditionIntersectionInclusion_closed _ _

def truncatedGradedProjection (d : Fin (B + 1)) :
    truncatedGradedParameters.{u, v} σ B r S ⟶
      Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d (r d) S :=
  truncatedGradedInclusion σ B r S ≫ QuotientParameters.truncatedQuotientProjection σ B r S d

theorem truncatedGradedParameters_universal {T : Over S}
    (q : ∀ d : Fin (B + 1), T ⟶ Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d (r d) S) :
    (∀ a : Fin B × σ, QuotientParameters.truncatedQuotientTupleMap σ B r q ∈
      (truncatedMultiplicationSubfunctor.{u, v} σ B r S a).obj (.op T)) ↔
        ∃! g : T ⟶ truncatedGradedParameters.{u, v} σ B r S,
          ∀ d : Fin (B + 1), g ≫ truncatedGradedProjection σ B r S d = q d := by
  have h := (Closed.ConditionIntersections.closedConditionIntersectionModel
    (truncatedMultiplicationSubfunctor.{u, v} σ B r S)
    (truncatedMultiplicationClosedModel σ B r S)).factorization T
      (QuotientParameters.truncatedQuotientTupleMap σ B r q)
  have he (g : T ⟶ truncatedGradedParameters.{u, v} σ B r S) :
      g ≫ truncatedGradedInclusion σ B r S = QuotientParameters.truncatedQuotientTupleMap σ B r q ↔
        ∀ d : Fin (B + 1), g ≫ truncatedGradedProjection σ B r S d = q d := by
    constructor
    · intro hg d
      change g ≫ (truncatedGradedInclusion σ B r S ≫ QuotientParameters.truncatedQuotientProjection σ B r S d) = _
      rw [← Category.assoc, hg, QuotientParameters.truncatedQuotientTupleMap_projection]
    · intro hg
      apply Pi.hom_ext
      intro d
      exact (Category.assoc _ _ _).trans ((hg d).trans
        (QuotientParameters.truncatedQuotientTupleMap_projection σ B r q d).symm)
  exact h.trans (existsUnique_congr he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GradedParameters
