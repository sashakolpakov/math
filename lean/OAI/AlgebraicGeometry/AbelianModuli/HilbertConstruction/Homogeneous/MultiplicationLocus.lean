import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LiftedHomogeneousMatrices
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceFamilies

/-! # Multiplication Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationLocus

noncomputable section

/-!
The actual closed locus imposing all variable-multiplication incidences between
two consecutive homogeneous quotient parameters, with its universal property.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (σ : Type v) [Finite σ] (d r s : ℕ)
variable {S : Scheme.{max u v}} {M : Over S}
variable (q : M ⟶ QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ d r S)
variable (k : M ⟶ QuotientParameters.homogeneousQuotientParameterScheme.{u, v} σ (d + 1) s S)

def homogeneousMultiplicationLocus : Over S :=
  Grassmann.IncidenceFamilies.grassmannIncidenceFamilyScheme q k
    (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} Γ(M.left, ⊤) σ d)

def homogeneousMultiplicationLocusInclusion : homogeneousMultiplicationLocus σ d r s q k ⟶ M :=
  Grassmann.IncidenceFamilies.grassmannIncidenceFamilyInclusion q k
    (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} Γ(M.left, ⊤) σ d)

instance homogeneousMultiplicationLocusInclusion_closed :
    IsClosedImmersion (homogeneousMultiplicationLocusInclusion σ d r s q k).left :=
  Grassmann.IncidenceFamilies.grassmannIncidenceFamilyInclusion_closed q k _

theorem homogeneousMultiplicationLocus_universal {T : Over S} (x : T ⟶ M) :
    (∀ i : σ, Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k
      (LiftedHomogeneousMatrices.liftedHomogeneousMultiplicationMatrix.{u, v} Γ(M.left, ⊤) σ d i) x) ↔
      ∃! g : T ⟶ homogeneousMultiplicationLocus σ d r s q k,
        g ≫ homogeneousMultiplicationLocusInclusion σ d r s q k = x :=
  Grassmann.IncidenceFamilies.grassmannIncidenceFamily_universal q k _ x

def homogeneousMultiplicationLocusProjective (P : Projective.ProjectivePresentations.ProjectivePresentation M) :
    Projective.ProjectivePresentations.ProjectivePresentation (homogeneousMultiplicationLocus σ d r s q k) :=
  Grassmann.IncidenceFamilies.grassmannIncidenceFamilyProjectivePresentation q k _ P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.MultiplicationLocus
