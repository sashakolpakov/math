import OAI.RepresentationTheory.Theta.Geometric.Relative.HodgeLevel
import OAI.RepresentationTheory.Theta.Geometric.Relative.HodgeAction

/-! # Level Iso -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The constructed fiber comparison is an isomorphism of the original
polarized full-level objects, including their represented duals. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] Intrinsic.CompatibleTransport.NativeCompatibleTransport.polarizedIso

variable {E : Type} [Field E] [NumberField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left)
    (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (D : Intrinsic.CompatibleTransport.NativeCompatibleTransport A ρ F) (z w : D.neighborhood)
    (hH : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C w)).variety)
      (D.rationalBetween A ρ z w).toLinearMap)

def Intrinsic.CompatibleTransport.NativeCompatibleTransport.levelIso : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left)
    (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left) := by
  let : IsMonHom (D.polarizedIso A ρ z w hH).hom := D.polarizedIso_group A ρ z w hH
  exact {
    abelian := D.polarizedIso A ρ z w hH
    dual := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).dual
      (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).dual (D.polarizedIso A ρ z w hH)
    abelianGroup := D.polarizedIso_group A ρ z w hH
    dualGroup := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso.dualFamilyIso_isMonHom (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).dual
      (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).dual (D.polarizedIso A ρ z w hH)
    polarization := D.polarizedIso_polarization A ρ z w hH
    poincare := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso.dualFamilyIso_poincare (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).dual
      (A.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).dual (D.polarizedIso A ρ z w hH)
    level := D.polarizedIso_level A ρ z w hH }

theorem Intrinsic.CompatibleTransport.NativeCompatibleTransport.levelIso_action (a : NumberField.RingOfIntegers E) :
    (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C z).left).map a ≫ (D.levelIso A ρ z w hH).abelian.hom =
      (D.levelIso A ρ z w hH).abelian.hom ≫ (ρ.pullback (Intrinsic.FamilyFrames.familyChartParameter C w).left).map a :=
  D.polarizedIso_action A ρ z w hH a

end

end OAI.RepresentationTheory.Theta.Geometric
