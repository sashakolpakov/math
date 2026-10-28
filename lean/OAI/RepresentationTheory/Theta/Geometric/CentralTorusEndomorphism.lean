import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusMap
import OAI.RepresentationTheory.Theta.Geometric.ChartEndomorphismExponential
import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts

/-! # Central Torus Endomorphism -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! An original family endomorphism acts on the fixed central torus
through the actual central fiber, with its exact derivative on periods. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance CentralTorusEndomorphism.centralTorusEndomorphism_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusEndomorphism
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (k : G.scheme ⟶ G.scheme) : C(F.CentralTorus, F.CentralTorus) :=
  ⟨fun t => (F.centralTorusHomeomorph P).symm
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))
      (F.centralTorusHomeomorph P t)),
    (F.centralTorusHomeomorph P).symm.continuous.comp
      ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map _).comp (F.centralTorusHomeomorph P).continuous)⟩

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.centralTorusEndomorphism_mk
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (k : G.scheme ⟶ G.scheme) [IsMonHom k]
    (D : Intrinsic.FamilyFrames.FamilyChartTangent C →L[ℝ] Intrinsic.FamilyFrames.FamilyChartTangent C) :
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
    let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
    (∀ v, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C))
      (F.charts (Intrinsic.FamilyFrames.familyChartCenter C)) (D v) =
        mfderiv (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C))) (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C)))
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C)))) 1
          (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartTangentMap (E := Intrinsic.FamilyFrames.FamilyChartModel C (Intrinsic.FamilyFrames.familyChartCenter C))
            (F.charts (Intrinsic.FamilyFrames.familyChartCenter C)) v)) →
    ∀ v, F.centralTorusEndomorphism P k (QuotientAddGroup.mk v) = QuotientAddGroup.mk (D v) := by
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left := F.integral
  let : ∀ z : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C z) := F.t2
  dsimp only
  intro hD v
  let K := ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism S G k (Intrinsic.FamilyFrames.familyChartParameter C (Intrinsic.FamilyFrames.familyChartCenter C))
  let : IsMonHom K := ArithmeticGeometry.Descent.CMVariety.FamilyEndomorphismCharts.Abelian.FamilyPoints.fiberEndomorphism_group S G k _
  apply (F.centralTorusHomeomorph P).injective
  change (F.centralTorusHomeomorph P) ((F.centralTorusHomeomorph P).symm
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map K (F.centralTorusHomeomorph P (QuotientAddGroup.mk v)))) = _
  rw [Homeomorph.apply_symm_apply, F.centralTorusHomeomorph_mk, F.centralTorusHomeomorph_mk]
  exact ChartEndomorphismExponential.nativeChartDerivative_exp (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C))
    (F.charts (Intrinsic.FamilyFrames.familyChartCenter C)) K D hD v

end

end OAI.RepresentationTheory.Theta.Geometric
