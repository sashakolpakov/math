import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.SectionCoefficientUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointQuotientSquare

/-! # Point Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.PointCoordinates

noncomputable section

/-! The native finite-coefficient quotient onto the fixed point is
literal source-section evaluation in the actual affine section rings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.InternalHom OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
attribute [local instance] Finite.FlatCoefficientSections.quotientAlgebra Finite.FlatCoefficientSections.coefficientAlgebra Finite.FlatCoefficientSections.ambientAlgebra
variable {Z Y X A : Scheme.{u}} (s₀ : Z ⟶ Y) (f : Y ⟶ X) (i : X ⟶ A)
  [IsClosedImmersion i] [IsClosedImmersion ((s₀ ≫ f) ≫ i)]
  (U : A.Opens) (hU : IsAffineOpen U) {c m : ℕ}
  (s : Fin c → Γ(A, U)) (t : Fin m → Γ(A, U))
  (hst : KoszulPartial.Resolution.pointIdeal Γ(A, U) s t = ((s₀ ≫ f) ≫ i).ker.ideal ⟨U,hU⟩)

def coefficient : ModuleCat.of Γ(A, U) (Finite.FlatCoefficientSections.coefficientRing f i U) ⟶
    ModuleCat.of Γ(A, U) (Γ(A, U) ⧸ KoszulPartial.Resolution.pointIdeal Γ(A, U) s t) :=
  (Finite.FlatCoefficientSections.chartIso f i U hU).inv ≫
    (AffineOpen.InternalHom.sections U hU).map (Cech.SectionCoefficientUnit.sheafMap s₀ f i) ≫
      (Closed.PointQuotientSquare.pointQuotient (s₀ ≫ f) i U hU s t hst).hom

omit [IsClosedImmersion i] in
theorem evaluation (x : Finite.FlatCoefficientSections.coefficientRing f i U) :
    coefficient s₀ f i U hU s t hst x =
      (Closed.PointQuotientSquare.pointQuotient (s₀ ≫ f) i U hU s t hst).hom
        ((Affine.ChartSections.iso U hU
          (Cech.StructurePullbackUnit.coefficients (s₀ ≫ f) i)).hom
            (s₀.app (f ⁻¹ᵁ (i ⁻¹ᵁ U)) x)) := by
  have h := ConcreteCategory.congr_hom
    ((AffineOpen.LinearHom.sectionsIso U hU).hom.naturality
      (Cech.SectionCoefficientUnit.sheafMap s₀ f i))
      (show Γ(Cech.StructurePullbackUnit.coefficients f i, U) from x)
  change (Affine.ChartSections.iso U hU
      (Cech.StructurePullbackUnit.coefficients (s₀ ≫ f) i)).hom
        ((Cech.SectionCoefficientUnit.sheafMap s₀ f i).val.app (op U) x) =
    (AffineOpen.InternalHom.sections U hU).map (Cech.SectionCoefficientUnit.sheafMap s₀ f i)
      ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients f i)).hom x) at h
  change (Closed.PointQuotientSquare.pointQuotient (s₀ ≫ f) i U hU s t hst).hom
    ((AffineOpen.InternalHom.sections U hU).map (Cech.SectionCoefficientUnit.sheafMap s₀ f i)
      ((Affine.ChartSections.iso U hU (Cech.StructurePullbackUnit.coefficients f i)).hom x)) = _
  rw [← h]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteCoefficient.PointCoordinates
