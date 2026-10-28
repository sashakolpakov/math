import OAI.RepresentationTheory.Theta.Geometric.RealRationalEquivalence
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.RationalTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice

/-! # Frame Rational Equiv -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

section

/-! The original full rational period transport is an equivalence,
with exactly the previously used real and rational point formulas. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods

local instance FrameRationalEquiv.nativeFrameRationalEquiv_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : FamilyFrames.NativeFamilyPeriodFrame C)

def FamilyFrames.NativeFamilyPeriodFrame.nativeRationalEquiv (z : FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C (FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C z)) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety ≃ₗ[ℚ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P.variety :=
  RealRationalEquivalence.RealPeriodMaps.rationalEquiv (F.nativeRealTransport z hzN P₀ P) (F.nativeRealTransport_lattice z hz hzN P₀ P)

theorem FamilyFrames.NativeFamilyPeriodFrame.nativeRationalEquiv_apply (z : FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C (FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C z)) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety) :
    F.nativeRationalEquiv z hz hzN P₀ P v = F.nativeRationalTransport z hz hzN P₀ P v := rfl

theorem FamilyFrames.NativeFamilyPeriodFrame.nativeRationalEquiv_coe (z : FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C (FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C z)) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety) :
    (F.nativeRationalEquiv z hz hzN P₀ P v).val = F.nativeRealTransport z hzN P₀ P v.val := rfl

end

/-! The original rational equivalence preserves and reflects the
entire integral period lattice, in its native rational-span definition. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : FamilyFrames.NativeFamilyPeriodFrame C)

theorem FamilyFrames.NativeFamilyPeriodFrame.nativeRationalEquiv_integral (z : FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C (FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C z)) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety) :
    F.nativeRationalEquiv z hz hzN P₀ P v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods P.variety ↔ v ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods P₀.variety :=
  F.nativeRealTransport_lattice z hz hzN P₀ P v.val

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
