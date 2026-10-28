import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.GroupGraph
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionDataBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding

/-! # Changed Group Graph -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph

noncomputable section

/-! The actual base-changed projective presentation has uniform addition
and inversion graph polynomials at every field-valued point of every tame
base. No embedding is chosen anew on the fibers. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance changedGroupGraphProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

local instance changedGroupGraphProductFinitePresentation {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom := inferInstanceAs
      (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

def uniformAdditionGraphHilbertPolynomial (g : ℕ) (δ : Fin g → ℕ) : Polynomial ℚ :=
  (AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp
    (Polynomial.C (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ : ℚ) * Polynomial.X)

def uniformInversionGraphHilbertPolynomial (g : ℕ) (δ : Fin g → ℕ) : Polynomial ℚ :=
  (Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
    (Polynomial.C ((Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ * 2 : ℕ) : ℚ) * Polynomial.X)

private theorem powerSectionData_graphHilbert_iff
    {K : Type u} [Field K] {X Y : Over (Spec (.of K))}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
    {P : Projective.ProjectivePresentations.ProjectivePresentation X} {Q : Projective.ProjectivePresentations.ProjectivePresentation Y}
    {L : Line.Bundles.LineBundle X.left} {M : Line.Bundles.LineBundle Y.left} {d : ℕ}
    (D : P.SectionData (L.tensorPower d)) (E : Q.SectionData (M.tensorPower d))
    (p : X ⟶ Y) (poly : Polynomial ℚ) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (P.product Q).embedding poly p ↔
      ((L.tensor (M.pullback p.left)).tensorPower d).HasSectionHilbertPolynomial X.hom poly :=
  (D.graphHilbertPolynomial_iff E p poly).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso X.hom _ _
      (Power.GraphPresentationTwisting.graphTensorPowerIso p L M d) poly)

namespace PolarizedAbelianWithFullLevel
variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
variable (K : Type u) [Field K] (x : Spec (.of K) ⟶ S)

local instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pulledGraphFlat : Flat ((Over.pullback x).obj A.abelian.scheme).hom :=
  inferInstanceAs (Flat (A.pullback x).abelian.scheme.hom)
local instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pulledGraphFinitePresentation :
    LocallyOfFinitePresentation ((Over.pullback x).obj A.abelian.scheme).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (A.pullback x).abelian.scheme.hom)
local instance _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pulledGraphSeparated : IsSeparated ((Over.pullback x).obj A.abelian.scheme).hom :=
  inferInstanceAs (IsSeparated (A.pullback x).abelian.scheme.hom)

include hg hN hunit

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.baseChangedInversionGraph_hilbertPolynomial :
    let P := E.projectivePresentation.baseChange x
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (P.product P).embedding
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
        (Polynomial.C ((E.degree * 2 : ℕ) : ℚ) * Polynomial.X)) ι[(A.pullback x).abelian.scheme] := by
  let B := A.pullback x
  let P := E.projectivePresentation.baseChange x
  let D := A.graphEmbeddingBaseChangeSectionData E x
  exact (powerSectionData_graphHilbert_iff (L := B.graphBundle) (M := B.graphBundle)
    (d := E.degree) D D ι[B.abelian.scheme] _).mpr
    (B.inversionGraphBundle_positivePower_hilbertPolynomial hg hN
      (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit x) E.degree E.degree_pos)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.baseChangedAdditionGraph_hilbertPolynomial :
    let P := E.projectivePresentation.baseChange x
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial ((P.product P).product P).embedding
      ((AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp
        (Polynomial.C (E.degree : ℚ) * Polynomial.X)) μ[(A.pullback x).abelian.scheme] := by
  let B := A.pullback x
  let P := E.projectivePresentation.baseChange x
  let D := A.graphEmbeddingBaseChangeSectionData E x
  exact (powerSectionData_graphHilbert_iff
    (L := Graph.ExternalTensorBundle.externalTensorBundle B.graphBundle B.graphBundle) (M := B.graphBundle)
    (d := E.degree) (D.productPowers D) D μ[B.abelian.scheme] _).mpr
    (A.pulledBackAdditionGraphBundle_positivePower_hilbertPolynomial_allFields hg hN hunit K x
      E.degree E.degree_pos)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.baseChangedUniformGroupGraphs_hilbertPolynomials
    (hE : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) :
    let P := E.projectivePresentation.baseChange x
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial ((P.product P).product P).embedding
      (uniformAdditionGraphHilbertPolynomial g δ) μ[(A.pullback x).abelian.scheme] ∧
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (P.product P).embedding
      (uniformInversionGraphHilbertPolynomial g δ) ι[(A.pullback x).abelian.scheme] := by
  constructor
  · simpa only [uniformAdditionGraphHilbertPolynomial, hE] using
      A.baseChangedAdditionGraph_hilbertPolynomial hg hN hunit E K x
  · simpa only [uniformInversionGraphHilbertPolynomial, hE] using
      A.baseChangedInversionGraph_hilbertPolynomial hg hN hunit E K x

end PolarizedAbelianWithFullLevel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph
