import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PolarizedAutomorphismGraphBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.SourcePolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ScaledTwistHilbertPolynomial

/-! # Automorphism Source Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismSourcePolynomial

noncomputable section

/-! The graph polynomial of any polarized automorphism is the source
fiber polynomial evaluated at twice the degree. It is chosen before the
automorphism, field extension, and Segre presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def polarizedAutomorphismGraphPolynomial {S : Scheme.{0}} {X : Over S}
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) (x : S) : Polynomial ℚ :=
  (Relative.SourcePolynomial.PolarizationEmbedding.e34SourceHilbertPolynomial B x).comp (Polynomial.C 2 * Polynomial.X)

theorem polarizedAutomorphismGraphPolynomial_isLocallyConstant
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S] {X : Over S} [Flat X.hom]
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X) :
    IsLocallyConstant (polarizedAutomorphismGraphPolynomial B) :=
  (Relative.SourcePolynomial.PolarizationEmbedding.e34SourceHilbertPolynomial_isLocallyConstant B).comp
    (fun P => P.comp (Polynomial.C 2 * Polynomial.X))

theorem polarized_automorphism_field_graph_source_polynomial
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme))
    (hB : HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) B)
    {K : Type} [Field K] (a : Spec (.of K) ⟶ S)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback a) (A.pullback a)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
      (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a e.abelian.hom).ker).toIdeal
        (polarizedAutomorphismGraphPolynomial (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
          (a (IsLocalRing.closedPoint K))) := by
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  let j := Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding BA a
  let v := e.abelian.hom
  let f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a v
  have : IsClosedImmersion j := Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_closed BA a
  have : IsClosedImmersion f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B a v
  have hb : f ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) =
      j ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := K) :=
    (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over A.abelian B a v).trans
      (Relative.FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_over BA a).symm
  have hv := Relative.PolarizedAutomorphismGraphBounds.geometric_polarized_automorphism_preserves_embedding_line A a P d hP e
  apply ScaledTwistHilbertPolynomial.PolarizationEmbedding.e34HilbertPolynomial_of_scaled_twists j f hb 2 (by decide)
    _ _ (Relative.SourcePolynomial.PolarizationEmbedding.relativeFieldSourceEmbedding_hasHilbertPolynomial BA a)
  intro m
  obtain ⟨b⟩ := Relative.FieldGraphTwists.PolarizationEmbedding.relativeFieldGraphEmbedding_twists A.abelian B a v P s hs he hB 0 m
  obtain ⟨q⟩ := Relative.GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct_power A.abelian (Over.mk a) v P 1 m
    (hv.trans (pow_one _).symm)
  obtain ⟨t⟩ := Relative.FieldSourceTwists.PolarizationEmbedding.relativeFieldSourceEmbedding_twists A.abelian.scheme P s hs he a 0 (2 * m)
  exact ⟨b ≪≫ q ≪≫ t.symm⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.AutomorphismSourcePolynomial
