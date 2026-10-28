import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.FiberHomeomorph
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.PresentedTangents

/-! # Real Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Native real transport between the central and nearby presented
fibers is the same exact period-frame transport, with its full lattice. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped Classical _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

local instance IntrinsicFrame.RealTransport.nativeFrameRealTransport_varietyIntegral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x}

variable (F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeRealTransport (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P₀.variety ≃L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P.variety :=
  (F.presentedChartTangent (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C) P₀).symm.trans
    ((F.realTransport z).trans (F.presentedChartTangent z hzN P))

def Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeFiberTransport (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P₀.variety.toOver ≃ₜ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.variety.toOver :=
  (F.presentedTorusHomeomorph (Intrinsic.FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀).symm.trans
    (F.presentedTorusHomeomorph z hz hzN P)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeRealTransport_lattice (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P₀.variety) :
    F.nativeRealTransport z hzN P₀ P v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P.variety ↔ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P₀.variety := by
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, IsIntegral (Intrinsic.FamilyFrames.familyChartFiber C w).scheme.left := F.integral
  let : ∀ w : Intrinsic.FamilyFrames.FamilyChartBase C, T2Space (Intrinsic.FamilyFrames.FamilyChartPoints C w) := F.t2
  let T₀ := F.presentedChartTangent (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C) P₀
  have h₀ := F.presentedChartTangent_lattice (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C) P₀ (T₀.symm v)
  have hz' := F.presentedChartTangent_lattice z hzN P (F.realTransport z (T₀.symm v))
  have ht := F.realTransport_lattice z hz (T₀.symm v)
  have he : T₀ (T₀.symm v) = v := T₀.apply_symm_apply v
  change T₀ (T₀.symm v) ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice P₀.variety ↔ T₀.symm v ∈ F.centralLattice at h₀
  rw [he] at h₀
  exact hz'.trans (ht.trans h₀.symm)

theorem Intrinsic.FamilyFrames.NativeFamilyPeriodFrame.nativeFiberTransport_period (z : Intrinsic.FamilyFrames.FamilyChartBase C) (hz : z ∈ F.neighborhood)
    (hzN : z ∈ C.charts.charts.neighborhood)
    (P₀ : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C (Intrinsic.FamilyFrames.familyChartCenter C)))
    (P : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ComplexAbelianPresentation (Intrinsic.FamilyFrames.familyChartFiber C z)) (v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel P₀.variety) :
    F.nativeFiberTransport z hz hzN P₀ P
      (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input P₀.variety (QuotientAddGroup.mk v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input P.variety
          (QuotientAddGroup.mk (F.nativeRealTransport z hzN P₀ P v)) := by
  let T₀ := F.presentedChartTangent (Intrinsic.FamilyFrames.familyChartCenter C) (Family.ChartOpenImage.familyChartCenter_mem C) P₀
  let u := T₀.symm v
  let e₀ := F.presentedTorusHomeomorph (Intrinsic.FamilyFrames.familyChartCenter C) F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀
  have h₀ : e₀ (QuotientAddGroup.mk u) =
      AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input P₀.variety (QuotientAddGroup.mk v) := by
    rw [F.presentedTorusHomeomorph_apply,
      F.presentedTorusMap_mk _ F.center (Family.ChartOpenImage.familyChartCenter_mem C) P₀, F.realTransport_central]
    exact congrArg (fun w => AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input P₀.variety (QuotientAddGroup.mk w))
      (T₀.apply_symm_apply v)
  rw [← h₀]
  change (F.presentedTorusHomeomorph z hz hzN P) (e₀.symm (e₀ (QuotientAddGroup.mk u))) = _
  rw [e₀.symm_apply_apply, F.presentedTorusHomeomorph_apply, F.presentedTorusMap_mk z hz hzN P]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric
