import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.SourceHilbertPolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphTwists
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolarizationLineBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldBaseCoefficients

/-! # Geometric Field Graph Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! One actual CM graph polynomial works for every algebraically closed
field extension, every Rosati-compatible action over that extension, and
every Presentations Segre presentation of the fixed source embedding. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem GeneratorReconstruction.CMIntegralGeneratorData.exists_uniform_geometric_field_graph_polynomial
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : GeneratorReconstruction.CMIntegralGeneratorData E)
    {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k))) :
    ∃ (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.abelian.scheme) (Q : Polynomial ℚ),
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B →
        ∀ (K : Type) [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ Spec (.of k))
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback a).abelian),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback a) ρ →
          HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
            (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a (ρ.map D.generator)).ker).toIdeal Q := by
  classical
  obtain ⟨d, _, P, hP, n, s, hs, he, Q, b, hQ⟩ :=
    D.exists_fixed_section_embedding_and_source_polynomial A
  let BA := SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he
  refine ⟨BA, Q, fun B hSegre K _ _ a ρ hρ => ?_⟩
  let v := ρ.map D.generator
  let f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a v
  have hclosed : IsClosedImmersion f := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B a v
  let := hclosed
  let L (m : ℕ) := ((P.tensorPower ((D.multiplier ^ 2 + 1) * m)).pullback
    (pullback.fst A.abelian.scheme.hom a)).sheaf
  have hv := D.baseChanged_polarization_power A a P d hP ρ hρ
  have htwists (m : ℕ) : Nonempty ((Scheme.Modules.pullback f).obj
      (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) (0 : Fin (B.dimension + 1)) m) ≅ L m) := by
    obtain ⟨e⟩ := Relative.FieldGraphTwists.PolarizationEmbedding.relativeFieldGraphEmbedding_twists A.abelian B a v P s hs he hSegre 0 m
    obtain ⟨q⟩ := Relative.GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct_power A.abelian (Over.mk a) v P (D.multiplier ^ 2) m hv
    exact ⟨e ≪≫ q⟩
  have hsections : ∃ c : ℕ, ∀ m : ℕ, c ≤ m →
      (Module.finrank Γ(Spec (.of K), ⊤)
        ((SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (A.pullback a).abelian.scheme.hom).obj (L m)) : ℚ) = Q.eval (m : ℚ) := by
    refine ⟨b, fun m hm => ?_⟩
    have hd := FieldBaseCoefficients.PolarizationEmbedding.fieldBaseCoefficients_lineSections_finrank A.abelian.scheme
      (P.tensorPower ((D.multiplier ^ 2 + 1) * m)) a
    exact (congrArg (fun z : ℕ => (z : ℚ)) hd).trans (hQ m hm)
  exact SourcePowerHilbertPolynomial.PolarizationEmbedding.e34HilbertPolynomial_of_eventual_sections f (A.pullback a).abelian.scheme.hom
    (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over A.abelian B a v) 0 L htwists Q hsections

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
