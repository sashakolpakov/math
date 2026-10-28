import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.FrameRationalEquiv

/-! # Rational Inverse -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic

noncomputable section

/-! The inverse of the original rational period equivalence has
exactly the inverse real map as its literal tangent-space value. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical

local instance RationalInverse.nativeRationalInverse_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

theorem RationalInverse.RealPeriodMaps.rationalEquiv_symm_coe {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
    (T : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (h : ∀ v, T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B ↔ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods B) :
    ((RealRationalEquivalence.RealPeriodMaps.rationalEquiv T h).symm v).val = T.symm v.val := rfl

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : FamilyFrames.NativeFamilyPeriodFrame C)

theorem FamilyFrames.NativeFamilyPeriodFrame.nativeRationalEquiv_symm_coe (z : FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C (FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (FamilyFrames.familyChartFiber C z)) (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods P.variety) :
    ((F.nativeRationalEquiv z hz hzN P₀ P).symm v).val =
      (F.nativeRealTransport z hzN P₀ P).symm v.val :=
  RationalInverse.RealPeriodMaps.rationalEquiv_symm_coe _ _ v

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic
