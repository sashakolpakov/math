import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieChartConormal
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankQuotientCriterion

/-! # Lie Rank Conormal Criterion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankConormalCriterion

noncomputable section

/-! ReferenceFamily's literal Lie rank on a geometric fiber is the fiber
dimension of the constructed conormal quotient on an actual action chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

namespace AlgebraicLie

variable {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (C : Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left
    (fun i => (ρ.map (IntegralModel.Finite.Actions.integralActionBasis E i)).left))
  {k : Type} [Field k] (q : Spec (.of k) ⟶ C.V.toScheme)

theorem hasLieRank_iff_chart_quotient
    (τ : NumberField.RingOfIntegers E →+* k)
    (t : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) → Γ(C.V.toScheme, ⊤))
    (hτ : ∀ i, τ (IntegralModel.Finite.Actions.integralActionBasis E i) = HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q (t i)) (r : ℕ) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.pullback (q ≫ C.V.ι)) (ρ.pullback (q ≫ C.V.ι)) τ r ↔
      Module.finrank k (k ⊗[Γ(C.V.toScheme, ⊤)]
        ConormalEigenquotient.conormalEigenquotient
          (C.conormalOperator (AbelianConormalCharts.abelian_unit_section A) (AbelianConormalCharts.action_over A ρ (IntegralModel.Finite.Actions.integralActionBasis E))
            (AbelianConormalCharts.action_unit_section A ρ (IntegralModel.Finite.Actions.integralActionBasis E))) t) = r := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := Affine.SectionLie.AffineSectionLie.baseFieldAlgebra q
  let : Module.Finite Γ(C.V.toScheme, ⊤) (RingHom.ker C.targetSection.appTop.hom).Cotangent :=
    (C.conormal_finite_projective (AbelianConormalCharts.abelian_unit_section A)).1
  let d := C.conormalOperator (AbelianConormalCharts.abelian_unit_section A) (AbelianConormalCharts.action_over A ρ (IntegralModel.Finite.Actions.integralActionBasis E))
    (AbelianConormalCharts.action_unit_section A ρ (IntegralModel.Finite.Actions.integralActionBasis E))
  let e := LieChartConormal.AlgebraicLie.chartConormalEquiv A ρ (IntegralModel.Finite.Actions.integralActionBasis E) C q
  exact LieRankQuotientCriterion.AlgebraicLie.hasLieRank_iff_conormal_quotient (A.pullback (q ≫ C.V.ι)) (ρ.pullback (q ≫ C.V.ι))
    τ d t e (LieChartConormal.AlgebraicLie.chartConormalEquiv_intertwines A ρ (IntegralModel.Finite.Actions.integralActionBasis E) C q) hτ r

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankConormalCriterion
