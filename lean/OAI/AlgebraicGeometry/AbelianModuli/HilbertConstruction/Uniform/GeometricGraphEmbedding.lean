import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphEmbeddingPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.NormalizedGraphPolynomial

/-! # Geometric Graph Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every field-valued fiber of any tame base has the same explicit graph
embedding degree, ambient dimension, and Hilbert polynomial. The Hilbert
condition includes every further extension of the field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial (g : ℕ) (δ : Fin g → ℕ) : Polynomial ℚ :=
  (Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
    (Polynomial.C (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ : ℚ) * Polynomial.X)

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))

def PolarizationData.PolarizedAbelianWithFullLevel.fieldPointUniformGraphEmbedding (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (A.pullback f).graphBundle (A.pullback f).abelian.scheme.hom :=
  (A.pullback f).uniformGraphPowerEmbedding hg hδ hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit f)

theorem PolarizationData.PolarizedAbelianWithFullLevel.fieldPointUniformGraphEmbedding_degree (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    (A.fieldPointUniformGraphEmbedding hg hδ hN hunit K f).degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ := rfl

theorem PolarizationData.PolarizedAbelianWithFullLevel.fieldPointUniformGraphEmbedding_dimension (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    (A.fieldPointUniformGraphEmbedding hg hδ hN hunit K f).dimension =
      Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 := rfl

local instance PolarizationData.PolarizedAbelianWithFullLevel.fieldPointEmbeddingFlat (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    Flat (Over.mk (A.pullback f).abelian.scheme.hom).hom :=
  inferInstanceAs (Flat (A.pullback f).abelian.scheme.hom)
local instance PolarizationData.PolarizedAbelianWithFullLevel.fieldPointEmbeddingFinitePresentation (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    LocallyOfFinitePresentation (Over.mk (A.pullback f).abelian.scheme.hom).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (A.pullback f).abelian.scheme.hom)

theorem PolarizationData.PolarizedAbelianWithFullLevel.fieldPointUniformGraphEmbedding_hilbertPolynomial
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ S) :
    let E := A.fieldPointUniformGraphEmbedding hg hδ hN hunit K f
    letI : IsClosedImmersion
        (SectionsProjectiveMorphism.sectionProjectiveMorphism (A.pullback f).abelian.scheme.hom E.sections E.covers).left :=
      E.closedImmersion
    ∀ (F : Type u) [Field F] (x : Spec (.of F) ⟶ Spec (.of K)),
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial ((Closed.Families.FlatClosedFamily.ofEmbedding
        (SectionsProjectiveMorphism.sectionProjectiveMorphism (A.pullback f).abelian.scheme.hom E.sections E.covers)).affineProjectivePullback x).homogeneousIdeal.toIdeal
        (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) := by
  let E := A.fieldPointUniformGraphEmbedding hg hδ hN hunit K f
  let : IsClosedImmersion
      (SectionsProjectiveMorphism.sectionProjectiveMorphism (A.pullback f).abelian.scheme.hom E.sections E.covers).left :=
    E.closedImmersion
  exact (A.pullback f).graphBundle_powerEmbedding_hilbertPolynomial hg hN
        (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit f) E

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
