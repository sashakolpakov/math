import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.CoefficientChartIntegralAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoefficientPoints
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientDualAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.BasisLocalDualRelations

/-! # Chart Conormal Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChartConormalAction

noncomputable section

section

/-! Every localization of an actual action chart carries a compatible
integral action on the coefficient dual of its original conormal module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {O I : Type} [CommRing O] (ρ : ActionData.IntegralAction O A) (b : Module.Basis I ℤ O)
  (C : PELModuli.IntegralModel.Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left (fun i => (ρ.map (b i)).left))

theorem integralChartLocalDualAction (P : Ideal Γ(C.V.toScheme, ⊤)) [P.IsMaximal] :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    CoefficientDualAction.CoefficientDualActionExists b
      (C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ b) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ b))
      (Localization.AtPrime P) inferInstance := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let R := Γ(C.V.toScheme, ⊤)
  let q := Affine.CoefficientPoints.affineCoefficientPoint C.V.toScheme (algebraMap R (Localization.AtPrime P))
  have hq : Local.CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q =
      (inferInstance : Algebra R (Localization.AtPrime P)) := by
    change (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap q).toAlgebra = _
    rw [Affine.CoefficientPoints.affineCoefficientPoint_coefficients]
    exact toAlgebra_algebraMap
  have h : CoefficientDualAction.CoefficientDualActionExists b
      (C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ b) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ b))
      (Localization.AtPrime P) (Local.CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q) := by
    unfold CoefficientDualAction.CoefficientDualActionExists
    let := Local.CoefficientLieSpace.LocalCoefficientLie.baseCoefficientAlgebra q
    let : Module R (Localization.AtPrime P) := Algebra.toModule
    refine ⟨Local.CoefficientChartIntegralAction.LocalCoefficientChart.conormalDualAction A ρ b C q, ?_⟩
    intro i ℓ v
    exact (LinearMap.congr_fun
      (Local.CoefficientChartIntegralAction.LocalCoefficientChart.conormalDualAction_generator A ρ b C q i ℓ) v).symm
  exact CoefficientDualAction.coefficientDualActionExists_transport b
    (C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ b) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ b)) hq h

end

/-! The literal finite conormal operators on an actual abelian action
chart extend to an integral ring action over its original coefficient
ring. The proof detects the multiplication equations at local rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {O I : Type} [CommRing O] (ρ : ActionData.IntegralAction O A) (b : Module.Basis I ℤ O)
  (C : PELModuli.IntegralModel.Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left (fun i => (ρ.map (b i)).left))

theorem integralChartConormalRelations :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    BasisActionRelations.IntegralBasisActionRelations b
      (C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ b) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ b)) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let R := Γ(C.V.toScheme, ⊤)
  let V := (RingHom.ker C.targetSection.appTop.hom).Cotangent
  let : Module.Finite R V := (C.conormal_finite_projective (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)).1
  let : Module.Projective R V := (C.conormal_finite_projective (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)).2
  apply CoefficientDualAction.integralBasisActionRelations_of_coefficientDualActions (R := R) b
  intro P hP
  exact integralChartLocalDualAction A ρ b C P

def integralChartConormalAction :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    O →+* Module.End Γ(C.V.toScheme, ⊤) (RingHom.ker C.targetSection.appTop.hom).Cotangent := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  exact BasisActionRelations.ringHomOfIntegralBasis b _ (integralChartConormalRelations A ρ b C)

theorem integralChartConormalAction_basis (i : I) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    integralChartConormalAction A ρ b C (b i) =
      C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ b) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ b) i := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  exact BasisActionRelations.ringHomOfIntegralBasis_apply b _ (integralChartConormalRelations A ρ b C) i

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChartConormalAction
