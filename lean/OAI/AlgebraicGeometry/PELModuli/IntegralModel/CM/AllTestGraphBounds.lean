import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.FieldGraphBounds
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.GraphFiberCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ActionFunctor

/-! # All Test Graph Bounds -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM

noncomputable section

/-! The fixed CM graph polynomial satisfies Presentations's exact field-fiber
predicate on every test scheme over a geometric polarized abelian variety. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  (D : GeneratorReconstruction.CMIntegralGeneratorData E)
  {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))

theorem GeneratorReconstruction.CMIntegralGeneratorData.exists_e34_graph_bound_on_all_tests :
    ∃ (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.abelian.scheme) (Q : Polynomial ℚ),
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B →
        ∀ (T : Over (Spec (.of k)))
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom).abelian),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
          HilbertScheme.Presentations.Has.Core.HasFiberHilbertPolynomial B
            (HilbertScheme.Presentations.HomFunctor.Hom.graphFamily A.abelian.scheme A.abelian.scheme
              (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T (ρ.map D.generator))) Q := by
  classical
  obtain ⟨BA, Q, hQ⟩ := D.exists_uniform_field_graph_polynomial A
  refine ⟨BA, Q, fun B hB T ρ hρ => ?_⟩
  apply Presentations.GraphFiberCoordinates.graphFamily_hasFiberHilbertPolynomial_of_coordinates A.abelian.scheme A.abelian.scheme
    B (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A.abelian T (ρ.map D.generator)) Q
  intro K _ a
  let t : Over (Spec (.of k)) := Over.mk (a ≫ T.hom)
  let b : t ⟶ T := Over.homMk a rfl
  let σ := Integral.ActionScheme.restrictIntegralAction A.abelian ρ b
  let c := EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso A.abelian t
  let e := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding A.abelian B (a ≫ T.hom) (σ.map D.generator)
  have hclosed : IsClosedImmersion e := Relative.FieldGraphEmbeddings.PolarizationEmbedding.relativeFieldGraphEmbedding_closed A.abelian B _ _
  let := hclosed
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
    exact hQ B hB K (a ≫ T.hom) σ
      (RosatiRestriction.rosati_restrictIntegralAction (T := t) (U := T) (E := E) A ρ hρ b)

theorem GeneratorReconstruction.CMIntegralGeneratorData.exists_e34_integral_generator_bound_on_all_tests :
    ∃ (BA : HilbertScheme.Presentations.Has.Core.ProjectivePresentation A.abelian.scheme) (Q : Polynomial ℚ),
      ∀ (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.abelian.scheme ⨯ A.abelian.scheme)),
        HilbertScheme.Presentations.Segre.Open.Core.IsSegrePresentation BA BA B →
        ∀ (T : Over (Spec (.of k)))
          (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (A.pullback T.hom).abelian),
          AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation (A.pullback T.hom) ρ →
          HilbertScheme.Presentations.Has.Core.HasGraphPolynomials A.abelian.scheme A.abelian.scheme 1 B (fun _ => Q)
            ((HilbertScheme.Presentations.Endomorphisms.Core.forgetGroupLaw A.abelian.scheme 1).app (op T)
              ((Integral.ActionFunctor.integralGeneratorTupleMap A.abelian D).app (op T) ρ)) := by
  obtain ⟨BA, Q, hQ⟩ := D.exists_e34_graph_bound_on_all_tests A
  exact ⟨BA, Q, fun B hB T ρ hρ _ => hQ B hB T ρ hρ⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM
