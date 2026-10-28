import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.RestrictionNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.IntrinsicCoefficientHom

/-! # Unit Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.UnitNormalization

noncomputable section

/-! The native unit of the finite coefficient algebra is the literal
map q ↦ q · 1 in the actual affine coefficient modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.RestrictionNormalization
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra

variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
  (i : X ⟶ Z) [IsClosedImmersion i] (U : Z.Opens) (hU : IsAffineOpen U)

local instance : (RestrictionNormalization.scalarSheaf i).IsQuasicoherent := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.isInvertible_unit
  exact AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom i
local instance : (RestrictionNormalization.coefficientSheaf f i).IsQuasicoherent :=
  Finite.MapPureTrace.coefficients_quasicoherent f i

omit [IsFinite f] [IsClosedImmersion i] in
theorem chart_square :
    (AffineOpen.InternalHom.sections U hU).map (Cech.StructurePullbackUnit.sheafMap f i) ≫ (Finite.FlatCoefficientSections.chartIso f i U hU).hom =
      (RestrictionNormalization.scalarChartIso i U hU).hom ≫ Quotient.CoefficientEvaluation.point Γ(Z, U) (Finite.FlatCoefficientSections.quotientRing i U) (Finite.FlatCoefficientSections.coefficientRing f i U) 1 := by
  have h := (AffineOpen.LinearHom.sectionsIso U hU).inv.naturality
    (Cech.StructurePullbackUnit.sheafMap f i)
  change (AffineOpen.InternalHom.sections U hU).map (Cech.StructurePullbackUnit.sheafMap f i) ≫
      (Affine.ChartSections.iso U hU (RestrictionNormalization.coefficientSheaf f i)).inv =
    (Affine.ChartSections.iso U hU (RestrictionNormalization.scalarSheaf i)).inv ≫
      (Affine.ModuleExactSections.sections U).map (Cech.StructurePullbackUnit.sheafMap f i) at h
  change (AffineOpen.InternalHom.sections U hU).map (Cech.StructurePullbackUnit.sheafMap f i) ≫
      ((Affine.ChartSections.iso U hU (RestrictionNormalization.coefficientSheaf f i)).inv ≫ (Finite.FlatCoefficientSections.literalIso f i U).hom) = _
  rw [← Category.assoc, h, Category.assoc]
  apply ConcreteCategory.hom_ext
  intro x
  change (f.app (i ⁻¹ᵁ U)).hom
      ((Affine.ChartSections.iso U hU (RestrictionNormalization.scalarSheaf i)).inv x) =
    (f.app (i ⁻¹ᵁ U)).hom ((Affine.ChartSections.iso U hU (RestrictionNormalization.scalarSheaf i)).inv x) * 1
  exact (mul_one _).symm

omit [IsFinite f] [IsClosedImmersion i] in
theorem coefficient_one :
    Affine.IntrinsicCoefficientHom.coefficientIso U hU (RestrictionNormalization.coefficientSheaf f i)
      (Finite.FlatCoefficientSections.coefficientRing f i U) (Finite.FlatCoefficientSections.chartIso f i U hU)
        (show Γ(RestrictionNormalization.coefficientSheaf f i, U) from (1 : Γ(Y, f ⁻¹ᵁ (i ⁻¹ᵁ U)))) = 1 := by
  change (Affine.ChartSections.iso U hU (RestrictionNormalization.coefficientSheaf f i)).inv
    ((Affine.ChartSections.iso U hU (RestrictionNormalization.coefficientSheaf f i)).hom (1 : Γ(Y, f ⁻¹ᵁ (i ⁻¹ᵁ U)))) =
      (show Γ(RestrictionNormalization.coefficientSheaf f i, U) from (1 : Γ(Y, f ⁻¹ᵁ (i ⁻¹ᵁ U))))
  exact Iso.hom_inv_id_apply _ _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.UnitNormalization
