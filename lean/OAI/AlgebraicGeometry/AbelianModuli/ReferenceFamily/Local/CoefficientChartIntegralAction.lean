import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientChartAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientLieAction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AbelianConormalCharts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ActionTransport

/-! # Coefficient Chart Integral Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientChartIntegralAction.LocalCoefficientChart

noncomputable section

/-! On every actual simultaneous action chart, the coefficient dual of
the conormal module carries the original integral action. This comparison
uses local coefficient rings, including rings with nilpotents. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.AbelianConormalCharts

variable {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {R I : Type} [CommRing R] (ρ : ActionData.IntegralAction R A) (a : I → R)
  (C : PELModuli.IntegralModel.Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left (fun i => (ρ.map (a i)).left))
  {k : Type} [CommRing k] [IsLocalRing k] (q : Spec (.of k) ⟶ C.V.toScheme)

def familyConormalEquiv :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    CoefficientLieSpace.LocalCoefficientLie.Space A.scheme.hom η[A.scheme].left (q ≫ C.V.ι) ≃ₗ[k]
      ((RingHom.ker C.targetSection.appTop.hom).Cotangent →ₗ[Γ(C.V.toScheme, ⊤)] k) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  exact (CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv C q).symm.trans
    (CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.targetProjection C.targetSection
      (C.target_retraction (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)) q)

def conormalDualAction :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    R →+* Module.End k
      ((RingHom.ker C.targetSection.appTop.hom).Cotangent →ₗ[Γ(C.V.toScheme, ⊤)] k) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  exact Dual.ActionTransport.transportedDualAction (R := Γ(C.V.toScheme, ⊤)) (CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv C q)
    (CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.targetProjection C.targetSection
      (C.target_retraction (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)) q)
    (CoefficientLieAction.LocalCoefficientLie.action (q ≫ C.V.ι) A ρ)

theorem conormalDualAction_eq_transport :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    conormalDualAction A ρ a C q =
      Dual.ActionTransport.transportedDualAction (R := Γ(C.V.toScheme, ⊤)) (CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv C q)
        (CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.targetProjection C.targetSection
          (C.target_retraction (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)) q)
        (CoefficientLieAction.LocalCoefficientLie.action (q ≫ C.V.ι) A ρ) := rfl

theorem action_eq_map (r : R)
    (v : CoefficientLieSpace.LocalCoefficientLie.Space A.scheme.hom η[A.scheme].left (q ≫ C.V.ι)) :
    CoefficientLieAction.LocalCoefficientLie.action (q ≫ C.V.ι) A ρ r v =
      CoefficientLieNaturality.LocalCoefficientLie.map A.scheme.hom A.scheme.hom η[A.scheme].left η[A.scheme].left
        (q ≫ C.V.ι) (ρ.map r).left (ρ.map r).w
        (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ (fun _ : Unit => r) ()) v := by
  apply CoefficientLieNaturality.LocalCoefficientLie.point_injective A.scheme.hom η[A.scheme].left (q ≫ C.V.ι)
  exact (CoefficientLieAction.LocalCoefficientLie.action_point (q ≫ C.V.ι) A ρ r v).trans
    (CoefficientLieNaturality.LocalCoefficientLie.point_map A.scheme.hom A.scheme.hom η[A.scheme].left η[A.scheme].left
      (q ≫ C.V.ι) (ρ.map r).left (ρ.map r).w
      (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ (fun _ : Unit => r) ()) v).symm

theorem chartAction_intertwines (i : I)
    (v : CoefficientLieSpace.LocalCoefficientLie.Space C.targetProjection C.targetSection q) :
    CoefficientLieAction.LocalCoefficientLie.action (q ≫ C.V.ι) A ρ (a i) (CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv C q v) =
      CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv C q
        (CoefficientChartAction.LocalCoefficientChart.tangentOperator C q (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ a) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ a) i v) :=
  (action_eq_map A ρ a C q (a i) (CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv C q v)).trans
    (CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv_operator C q (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ a) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ a) i v).symm

theorem conormalDualAction_generator (i : I)
    (ℓ : letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
      letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
      (RingHom.ker C.targetSection.appTop.hom).Cotangent →ₗ[Γ(C.V.toScheme, ⊤)] k) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    letI := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    conormalDualAction A ρ a C q (a i) ℓ = ℓ.comp
      (C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ a) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ a) i) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let := CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
  have h := Dual.ActionTransport.transportedDualAction_generator (R := Γ(C.V.toScheme, ⊤)) (k := k) (O := R)
    (W := (RingHom.ker C.targetSection.appTop.hom).Cotangent) (CoefficientChartAction.LocalCoefficientChart.targetTangentEquiv C q)
    (CoefficientLieConormal.LocalCoefficientLie.conormalEquiv C.targetProjection C.targetSection
      (C.target_retraction (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)) q)
    (CoefficientLieAction.LocalCoefficientLie.action (q ≫ C.V.ι) A ρ) a
    (CoefficientChartAction.LocalCoefficientChart.tangentOperator C q (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ a) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ a))
    (C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ a) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ a))
    (chartAction_intertwines A ρ a C q)
    (CoefficientChartAction.LocalCoefficientChart.tangentOperator_conormal C q (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ a)
      (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ a)) i ℓ
  exact (congrArg (fun τ : R →+* Module.End k
    ((RingHom.ker C.targetSection.appTop.hom).Cotangent →ₗ[Γ(C.V.toScheme, ⊤)] k) => τ (a i) ℓ)
      (conormalDualAction_eq_transport A ρ a C q)).trans h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientChartIntegralAction.LocalCoefficientChart
