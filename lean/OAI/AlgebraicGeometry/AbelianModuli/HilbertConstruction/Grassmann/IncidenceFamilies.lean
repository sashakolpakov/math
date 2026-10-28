import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceUniversality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ConditionIntersections

/-! # Incidence Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceFamilies

noncomputable section

/-!
Simultaneous kernel preservation by a family of linear maps has a constructed
closed parameter scheme. In particular this imposes all coordinate
multiplication maps between two chosen graded quotient parameters at once.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {ι ν κ μ : Type u} {α : Type v}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M : Over S}
variable (q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : α → Matrix μ ν Γ(M.left, ⊤))

def grassmannIncidenceFamilyScheme : Over S :=
  Closed.ConditionIntersections.closedConditionIntersectionScheme (fun i => IncidenceUniversality.grassmannIncidenceSubfunctor q k (F i))
    (fun i => IncidenceUniversality.grassmannIncidenceClosedModel q k (F i))

def grassmannIncidenceFamilyInclusion : grassmannIncidenceFamilyScheme q k F ⟶ M :=
  Closed.ConditionIntersections.closedConditionIntersectionInclusion (fun i => IncidenceUniversality.grassmannIncidenceSubfunctor q k (F i))
    (fun i => IncidenceUniversality.grassmannIncidenceClosedModel q k (F i))

theorem grassmannIncidenceFamily_universal {T : Over S} (x : T ⟶ M) :
    (∀ i, IncidenceCondition.GrassmannIncidenceCondition q k (F i) x) ↔
      ∃! g : T ⟶ grassmannIncidenceFamilyScheme q k F,
        g ≫ grassmannIncidenceFamilyInclusion q k F = x :=
  (Closed.ConditionIntersections.closedConditionIntersectionModel (fun i => IncidenceUniversality.grassmannIncidenceSubfunctor q k (F i))
    (fun i => IncidenceUniversality.grassmannIncidenceClosedModel q k (F i))).factorization T x

instance grassmannIncidenceFamilyInclusion_closed :
    IsClosedImmersion (grassmannIncidenceFamilyInclusion q k F).left :=
  Closed.ConditionIntersections.closedConditionIntersectionInclusion_closed _ _

def grassmannIncidenceFamilyProjectivePresentation (P : Projective.ProjectivePresentations.ProjectivePresentation M) :
    Projective.ProjectivePresentations.ProjectivePresentation (grassmannIncidenceFamilyScheme q k F) :=
  P.ofClosedImmersion (grassmannIncidenceFamilyInclusion q k F)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceFamilies
