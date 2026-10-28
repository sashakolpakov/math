import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransportGroup
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.ChernMaps
import OAI.RepresentationTheory.Theta.Geometric.RealChernPairing

/-! # Rational Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual family-frame transport carries original native rational
periods and their Chern forms through the same continuous group map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

local instance IntrinsicFrame.RationalTransport.nativeFrameRationalTransport_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeRationalTransport (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety →ₗ[ℚ] AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P.variety :=
  RealPeriodCoe.RealPeriodMaps.rationalMap (F.nativeRealTransport z hzN P₀ P).toContinuousLinearMap
    (fun v hv => (F.nativeRealTransport_lattice z hz hzN P₀ P v).mpr hv)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeRationalTransport_coe (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety) :
    (F.nativeRationalTransport z hz hzN P₀ P v).val = F.nativeRealTransport z hzN P₀ P v.val := rfl

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeChernForm_transport (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z))
    (L₀ : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle P₀.variety.toOver.left) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle P.variety.toOver.left)
    (hc : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass P₀.variety.variety.presentation L₀ =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) (F.nativePointTransport z hz hzN P₀ P) 2
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass P.variety.variety.presentation L))
    (v w : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P₀.variety) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm P₀.variety L₀ v w = AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing.nativeChernForm P.variety L
      (F.nativeRationalTransport z hz hzN P₀ P v) (F.nativeRationalTransport z hz hzN P₀ P w) :=
  RealChernPairing.RealPeriodMaps.nativeChernForm_continuous_naturality
    (F.nativeRealTransport z hzN P₀ P).toContinuousLinearMap
    (fun u hu => (F.nativeRealTransport_lattice z hz hzN P₀ P u).mpr hu)
    (F.nativePointTransport z hz hzN P₀ P)
    (F.nativeFiberTransport_period z hz hzN P₀ P)
    (F.nativeFiberTransport_mul z hz hzN P₀ P) L₀ L hc v w

end

end OAI.RepresentationTheory.Theta.Geometric
