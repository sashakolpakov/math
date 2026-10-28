import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChartConormalAction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.CharacterQuotient

/-! # Chart Character Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChartCharacterQuotient

noncomputable section

/-! The character quotient of the literal affine conormal operators of
an abelian scheme with integral action is projective in characteristic
zero. No reducedness of the base is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem integralChartCharacterQuotient_projective
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    {I : Type} [Fintype I] (b : Module.Basis I ℤ (NumberField.RingOfIntegers E))
    (C : PELModuli.IntegralModel.Section.ActionCharts.SectionMorphismChart A.scheme.hom η[A.scheme].left (fun i => (ρ.map (b i)).left))
    [Algebra ℚ Γ(C.V.toScheme, ⊤)] (χ : NumberField.RingOfIntegers E →+* Γ(C.V.toScheme, ⊤)) :
    letI := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
    Module.Projective Γ(C.V.toScheme, ⊤) (PELModuli.IntegralModel.ConormalEigenquotient.conormalEigenquotient
      (C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ b) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ b))
      (fun i => χ (b i))) := by
  let := Divisors.LineBundles.Affine.SchemeSection.BundleCycles.AffineSchemeSection.baseAlgebra C.targetProjection
  let R := Γ(C.V.toScheme, ⊤)
  let V := (RingHom.ker C.targetSection.appTop.hom).Cotangent
  let : Module.Projective R V := (C.conormal_finite_projective (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A)).2
  let : Module ℚ V := Module.compHom V (algebraMap ℚ R)
  let : IsScalarTower ℚ R V := IsScalarTower.of_compHom ℚ R V
  have h := CharacterQuotient.integralCharacterQuotient_projective b (ChartConormalAction.integralChartConormalAction A ρ b C) χ
  have hd : (fun i => ChartConormalAction.integralChartConormalAction A ρ b C (b i)) =
      C.conormalOperator (PELModuli.IntegralModel.AbelianConormalCharts.abelian_unit_section A) (PELModuli.IntegralModel.AbelianConormalCharts.action_over A ρ b) (PELModuli.IntegralModel.AbelianConormalCharts.action_unit_section A ρ b) :=
    funext (ChartConormalAction.integralChartConormalAction_basis A ρ b C)
  rw [hd] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChartCharacterQuotient
