import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.TorusMap
import OAI.RepresentationTheory.Theta.Geometric.LinearQuotientHomeomorph
import OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation

/-! # Fiber Homeomorph -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual real frame transport identifies the fixed central torus
homeomorphically with every nearby original fiber and its presentation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

local instance IntrinsicFrame.FiberHomeomorph.nativeFrameFiberHomeomorph_nativeRealLieGroup (z : Intrinsic.FamilyFrames.FamilyChartBase C)
    [IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C z).scheme.left] :
    LieGroup (𝓘(ℝ, Intrinsic.FamilyFrames.FamilyChartModel C z)) ∞ (Intrinsic.FamilyFrames.FamilyChartPoints C z) :=
  ArithmeticGeometry.Descent.CMVariety.IntrinsicFiberLieGroup.Abelian.nativeScheme_realLieGroup (Intrinsic.FamilyFrames.familyChartFiber C z).scheme

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberHomeomorph (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) : F.CentralTorus ≃ₜ Intrinsic.FamilyFrames.FamilyChartPoints C z := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  let : ConnectedSpace (Intrinsic.FamilyFrames.FamilyChartPoints C z) := P.connectedSpace
  have hc := F.chartData z hzN
  exact (LinearQuotientHomeomorph.linearQuotientHomeomorph (F.realTransport z) F.centralLattice.toAddSubgroup
    (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := Intrinsic.FamilyFrames.FamilyChartModel C z) (F.charts z)).toAddSubgroup
    (F.realTransport_lattice z hz)).trans
      (Intrinsic.ChartQuotient.nativeChartQuotientHomeomorph (F.charts z) hc.2.2.1 hc.1 hc.2.1)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.torusFiberHomeomorph_apply (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : F.CentralTorus) :
    F.torusFiberHomeomorph z hz hzN P v = F.torusFiberMap z hz v := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  induction v using Quotient.inductionOn with
  | h v => rfl

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusHomeomorph (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    F.CentralTorus ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver :=
  (F.torusFiberHomeomorph z hz hzN P).trans (ArithmeticGeometry.Descent.CMVariety.IntrinsicDerivativeConjugation.Abelian.nativeSchemeIsoHomeomorph P.comparison)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusHomeomorph_apply (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : F.CentralTorus) :
    F.presentedTorusHomeomorph z hz hzN P v = F.presentedTorusMap z hz P v :=
  congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom) (F.torusFiberHomeomorph_apply z hz hzN P v)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.presentedTorusMap_add (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v w : F.CentralTorus) :
    F.presentedTorusMap z hz P (v + w) = F.presentedTorusMap z hz P v * F.presentedTorusMap z hz P w := by
  have h := congrArg (fun y : Additive (Intrinsic.FamilyFrames.FamilyChartPoints C z) =>
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map P.comparison.hom y.toMul) ((F.torusFiberHom z hz).map_add v w)
  exact h.trans (MonObj.mul_comp _ _ P.comparison.hom)

end

end OAI.RepresentationTheory.Theta.Geometric
