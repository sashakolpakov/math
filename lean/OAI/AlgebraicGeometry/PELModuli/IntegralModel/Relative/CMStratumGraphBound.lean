import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.CMGraphSourcePolynomial
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphFiberCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctor

/-! # CM Stratum Graph Bound -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! On each computed clopen base stratum, the exact Presentations graph-polynomial
predicate holds for every Rosati action on every test scheme. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    (D : CM.GeneratorReconstruction.CMIntegralGeneratorData E)
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

include hP hB in
theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.relative_e34_graph_polynomial_on_stratum
    (Q : Polynomial ℚ) (T : Over S)
    (hT : ∀ t : T.left, T.hom t ∈ Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) Q)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom).abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ) :
    HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial B
      (HilbertScheme.Presentations.HomFunctor.Hom.graphFamily A.abelian.scheme A.abelian.scheme
        (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T (ρ.map D.generator))) Q := by
  apply Presentations.GraphFiberCoordinates.graphFamily_hasFiberHilbertPolynomial_of_coordinates A.abelian.scheme A.abelian.scheme
    B (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T (ρ.map D.generator)) Q
  intro K _ a
  let t : Over S := Over.mk (a ≫ T.hom)
  let b : t ⟶ T := Over.homMk a rfl
  let σ := Integral.ActionScheme.restrictIntegralAction A.abelian ρ b
  let c := EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso A.abelian t
  let e := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B (a ≫ T.hom) (σ.map D.generator)
  have : IsClosedImmersion e := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B _ _
  have hr : EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian t (σ.map D.generator) =
      prod.map b (𝟙 A.abelian.scheme) ≫ EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T (ρ.map D.generator) :=
    EndomorphismHom.EndomorphismFamilies.relativeHom_restrict A.abelian b
      (Finite.Actions.ringHomOfIntegralAction (A.abelian.pullback T.hom) ρ D.generator)
  refine ⟨AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap (a ≫ T.hom) B.dimension, c.hom ≫ e,
    AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback (a ≫ T.hom) B.dimension, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · change (c.hom ≫ (c.inv ≫
      (HilbertScheme.Presentations.HomFunctor.Hom.graph A.abelian.scheme A.abelian.scheme (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian t (σ.map D.generator))).left ≫
        Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B (a ≫ T.hom))) ≫ _ = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_projective]
    rw [hr]
  · rw [Category.assoc, Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_over]
    exact EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso_snd A.abelian t
  · rw [Scheme.Hom.ker_comp_of_isIso]
    have hp := D.relative_field_graph_source_polynomial A P d hP s hs he B hB (a ≫ T.hom) σ
      (RosatiRestriction.rosati_restrictIntegralAction (T := t) (U := T) (E := E) A ρ hρ b)
    have hQ : Relative.CMGraphSourcePolynomial.relativeCMGraphPolynomial D (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he)
        ((a ≫ T.hom) (IsLocalRing.closedPoint K)) = Q := hT (a (IsLocalRing.closedPoint K))
    exact hQ ▸ hp

include hP hB in
theorem CM.GeneratorReconstruction.CMIntegralGeneratorData.relative_e34_integral_generator_on_stratum
    (Q : Polynomial ℚ) (T : Over S)
    (hT : ∀ t : T.left, T.hom t ∈ Relative.CMGraphSourcePolynomial.relativeCMPolynomialOpen D
      (SegreSectionPowers.PolarizationEmbedding.e34SectionPresentation A.abelian.scheme P s hs he) Q)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom).abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ) :
    HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.abelian.scheme A.abelian.scheme 1 B (fun _ => Q)
      ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.abelian.scheme 1).app (op T)
        ((Integral.ActionFunctor.integralGeneratorTupleMap A.abelian D).app (op T) ρ)) :=
  fun _ => D.relative_e34_graph_polynomial_on_stratum A P d hP s hs he B hB Q T hT ρ hρ

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
