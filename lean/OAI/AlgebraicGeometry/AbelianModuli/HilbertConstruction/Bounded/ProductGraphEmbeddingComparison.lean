import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ProductEmbeddingTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphTwistingInvariance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.EmbeddedMorphismFunctor

/-! # Product Graph Embedding Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The bounded morphism parameter's native Cartesian product embedding
has exactly the Hilbert condition computed using the product of the
base-changed projective presentations, on every test scheme. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

local instance Bounded.ProductGraphEmbeddingComparison.comparisonPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback f).obj X).hom := inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd X.hom f))

local instance Bounded.ProductGraphEmbeddingComparison.comparisonPullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S)
    [LocallyOfFinitePresentation X.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd X.hom f))

local instance Bounded.ProductGraphEmbeddingComparison.comparisonPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback f).obj X).hom :=
  inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd X.hom f))

variable {S T : Scheme.{u}} {X Y : Over S}
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
variable (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y)

theorem Projective.ProjectivePresentations.ProjectivePresentation.relativeProductGraph_hilbertPolynomial_iff
    (f : T ⟶ S) (R : Polynomial ℚ) (p : (Over.pullback f).obj X ⟶ (Over.pullback f).obj Y) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f (P.product Q).embedding) R p ↔
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial ((P.baseChange f).product (Q.baseChange f)).embedding R p :=
  Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.iff_of_twistingIso
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f (P.product Q).embedding)
    ((P.baseChange f).product (Q.baseChange f)).embedding
    (P.relativeProductEmbeddingTwistingIso Q f) R p

theorem Projective.ProjectivePresentations.ProjectivePresentation.boundedProductGraph_mem_iff (R : Polynomial ℚ) (T : Over S)
    (p : (Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y) :
    p ∈ (Bounded.EmbeddedMorphismFunctor.boundedEmbeddedMorphismSubfunctor (P.product Q).embedding R).obj (Opposite.op T) ↔
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial ((P.baseChange T.hom).product (Q.baseChange T.hom)).embedding R p :=
  P.relativeProductGraph_hilbertPolynomial_iff Q T.hom R p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
