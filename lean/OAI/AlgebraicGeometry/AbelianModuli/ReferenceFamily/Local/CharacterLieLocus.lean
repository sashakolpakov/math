import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChartCharacterQuotient
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.FlatRankLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankConormalCriterion
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankCharacter
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Character Lie Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CharacterLieLocus

noncomputable section

/-! The original geometric character Lie rank has an actual clopen
representing locus on every constructed action chart. Every test scheme
is classified, including nonreduced tests. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankCharacter

theorem exists_local_character_lie_locus
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {S : Scheme.{0}} [IsLocallyNoetherian S] {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (χ : NumberField.RingOfIntegers E →+* Γ(S, ⊤)) (r : ℕ)
    (C : PELModuli.IntegralModel.Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left
      (fun i => (ρ.map (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E i)).left))
    [Algebra ℚ Γ(C.V.toScheme, ⊤)] :
    ∃ (Z : Scheme.{0}) (j : Z ⟶ C.V.toScheme), IsOpenImmersion j ∧ IsClosedImmersion j ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ C.V.toScheme),
        (∀ (k : Type) [Field k] [IsAlgClosed k] (p : Spec (.of k) ⟶ T),
          PELModuli.IntegralModel.LieRankCharacter.CharacterLieRank A ρ χ r ((p ≫ x) ≫ C.V.ι)) ↔
            ∃! f : T ⟶ Z, f ≫ j = x := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let R := Γ(C.V.toScheme, ⊤)
  let V := (RingHom.ker C.targetSection.appTop.hom).Cotangent
  let : Module.Finite R V := (C.conormal_finite_projective (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)).1
  let : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top C.V.toScheme⟩
  let d := C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)
    (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E)) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E))
  let t := fun i => C.V.ι.appTop (χ (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E i))
  let Q := PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient d t
  let : Module.Projective R Q := Integral.ChartCharacterQuotient.integralChartCharacterQuotient_projective A ρ
    (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E) C (C.V.ι.appTop.hom.comp χ)
  let : Module.FinitePresentation R Q := PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient_finitePresentation d t
  obtain ⟨Z, j, hopen, hclosed, hclass⟩ := Affine.FlatRankLocus.exists_affine_flat_module_rank_locus C.V.toScheme Q r
  refine ⟨Z, j, hopen, hclosed, ?_⟩
  intro T x
  refine Iff.trans ?_ (hclass T x)
  have h (k : Type) [Field k] (q : Spec (.of k) ⟶ C.V.toScheme) :
      letI := PELModuli.IntegralModel.Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
      PELModuli.IntegralModel.LieRankCharacter.CharacterLieRank A ρ χ r (q ≫ C.V.ι) ↔ Module.finrank k (k ⊗[R] Q) = r := by
    apply PELModuli.IntegralModel.LieRankConormalCriterion.AlgebraicLie.hasLieRank_iff_chart_quotient A ρ C q
      ((HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap (q ≫ C.V.ι)).comp χ) t
    intro i
    exact RingHom.congr_fun (PELModuli.IntegralModel.TangentPointCoefficients.RelativeTangent.coefficientMap_postcomp q C.V.ι)
      (χ (PELModuli.IntegralModel.Finite.Actions.integralActionBasis E i))
  constructor
  · intro hx k hk ha p
    exact (h k (p ≫ x)).mp (hx k p)
  · intro hx k hk ha p
    exact (h k (p ≫ x)).mpr (hx k p)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CharacterLieLocus
