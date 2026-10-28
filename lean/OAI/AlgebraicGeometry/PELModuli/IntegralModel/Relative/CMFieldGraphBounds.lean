import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.PolarizedAutomorphismGraphBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldGraphBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RosatiRestriction
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # CM Field Graph Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The finite CM graph bound for a varying polarized family holds over
every field, by reflection of the actual graph polynomial from an
algebraic closure. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.exists_finite_relative_field_graph_polynomials
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
    {S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.abelian.scheme.left) (d : ℕ)
    (hP : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower (Relative.PoincareSimilitude.RelativePoincareClasses.polarizationLine A.dual
      A.polarization.isogeny.hom).sheaf d P.sheaf)
    {n : ℕ} (s : Fin (n + 1) → (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.abelian.scheme.left ⟶ P.sheaf))
    (hs : ∀ x : A.abelian.scheme.left, ∃ i, x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (s i))
    (he : IsClosedImmersion (AbelianModuli.HilbertConstruction.SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom s hs).left) :
    ∃ F : Finset (Polynomial ℚ),
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
          (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) B →
        ∀ (K : Type) [Field K] (a : Spec (.of K) ⟶ S)
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback a).abelian),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback a) ρ →
          ∃ Q ∈ F, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
            (Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B a (ρ.map D.generator)).ker).toIdeal Q := by
  classical
  obtain ⟨F, hF⟩ := D.exists_finite_relative_geometric_graph_polynomials A P d hP s hs he
  refine ⟨F, fun B hB K _ a ρ hρ => ?_⟩
  let L := AlgebraicClosure K
  let β := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let b : Over.mk (β ≫ a) ⟶ Over.mk a := Over.homMk β rfl
  let σ := Integral.ActionScheme.restrictIntegralAction A.abelian ρ b
  have hσ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback (β ≫ a)) σ :=
    RosatiRestriction.rosati_restrictIntegralAction (T := Over.mk (β ≫ a)) (U := Over.mk a)
      (E := E) A ρ hρ b
  obtain ⟨Q, hQ, hp⟩ := hF B hB L (β ≫ a) σ hσ
  exact ⟨Q, hQ, (FieldGraphBaseChange.PolarizationEmbedding.relativeIntegralGraph_hilbertPolynomial_baseChange_iff
    a (algebraMap K L) A.abelian B ρ D.generator Q).mp hp⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
