import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdditionGraphFieldPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.InversionBundle

/-! # Group Graph -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Hilbert polynomials below belong to the actual graph ideals in
the native nested Segre presentations of a chosen graph-power embedding. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
local instance PowerEmbedding.GroupGraph.groupGraphFieldProductFlat {S : Scheme.{u}} (X Y : Over S) [Flat X.hom] [Flat Y.hom] :
    Flat (X ⊗ Y).hom := inferInstanceAs (Flat (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

local instance PowerEmbedding.GroupGraph.groupGraphFieldProductFinitePresentation {S : Scheme.{u}} (X Y : Over S)
    [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom := inferInstanceAs
      (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

section
variable {K : Type u} [Field K] {X : Over (Spec (.of K))}
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
variable {L : Line.Bundles.LineBundle X.left} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom)

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.unaryGraph_hilbertPolynomial_iff (p : X ⟶ X) (P : Polynomial ℚ) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (E.projectivePresentation.product E.projectivePresentation).embedding P p ↔
      ((L.tensor (L.pullback p.left)).tensorPower E.degree).HasSectionHilbertPolynomial X.hom P :=
  (Relative.EmbeddingIntrinsic.embeddedGraph_intrinsicHilbertPolynomial_iff
    (E.projectivePresentation.product E.projectivePresentation).embedding P p).trans
      (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso X.hom _ _
        (E.unaryGraphSectionData p).twistingIso P)

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.binaryGraph_hilbertPolynomial_iff (p : X ⊗ X ⟶ X) (P : Polynomial ℚ) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      ((E.projectivePresentation.product E.projectivePresentation).product E.projectivePresentation).embedding P p ↔
    (((Graph.ExternalTensorBundle.externalTensorBundle L L).tensor (L.pullback p.left)).tensorPower E.degree).HasSectionHilbertPolynomial (X ⊗ X).hom P :=
  (Relative.EmbeddingIntrinsic.embeddedGraph_intrinsicHilbertPolynomial_iff
    ((E.projectivePresentation.product E.projectivePresentation).product E.projectivePresentation).embedding P p).trans
      (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso (X ⊗ X).hom _ _
        (E.binaryGraphSectionData p).twistingIso P)
end

theorem PolarizationData.PolarizedAbelianWithFullLevel.inversion_graphPowerEmbedding_hilbertPolynomial
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      (E.projectivePresentation.product E.projectivePresentation).embedding
      ((Normalized.GraphPolynomial.normalizedGraphHilbertPolynomial g δ).comp
        (Polynomial.C ((E.degree * 2 : ℕ) : ℚ) * Polynomial.X)) ι[A.abelian.scheme] :=
  (E.unaryGraph_hilbertPolynomial_iff ι[A.abelian.scheme] _).mpr
    (A.inversionGraphBundle_positivePower_hilbertPolynomial hg hN hNk E.degree E.degree_pos)

theorem PolarizationData.PolarizedAbelianWithFullLevel.pulledBackAddition_graphPowerEmbedding_hilbertPolynomial
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (hg : 0 < g) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (K : Type u) [Field K] (f : Spec (.of K) ⟶ S)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (A.pullback f).graphBundle (A.pullback f).abelian.scheme.hom) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial
      ((E.projectivePresentation.product E.projectivePresentation).product E.projectivePresentation).embedding
      ((AdditionGraphPolynomial.normalizedAdditionGraphHilbertPolynomial g δ).comp
        (Polynomial.C (E.degree : ℚ) * Polynomial.X)) μ[(A.pullback f).abelian.scheme] :=
  (E.binaryGraph_hilbertPolynomial_iff μ[(A.pullback f).abelian.scheme] _).mpr
    (A.pulledBackAdditionGraphBundle_positivePower_hilbertPolynomial_allFields hg hN hunit K f E.degree E.degree_pos)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
