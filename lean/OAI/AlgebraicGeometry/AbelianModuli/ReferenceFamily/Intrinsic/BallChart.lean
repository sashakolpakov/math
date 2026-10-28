import OAI.RepresentationTheory.Theta.Geometric.Family.IntrinsicChart
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.HolomorphicBallPeriods

/-! # Ball Chart -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallChart

noncomputable section

/-! Composing the actual native family chart with ball period coordinates
preserves the original scheme atlas and the exact inverse parameter map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.Manifold

open OAI.RepresentationTheory.Theta.Geometric.Family.IntrinsicChart

variable {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} (C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x)
    (q : OpenPartialHomeomorph (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C) Geometry.ComplexBall.PrescribedSignsB.BallChart)

def nativeFamilyBallChart : OpenPartialHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) Geometry.ComplexBall.PrescribedSignsB.BallChart :=
  (RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart C).trans q

theorem nativeFamilyBallChart_symm_apply (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    (nativeFamilyBallChart C q).symm z = RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (q.symm z) := rfl

theorem nativeFamilyBallChart_center_mem (hx : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ q.source) :
    x ∈ (nativeFamilyBallChart C q).source := by
  refine ⟨RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_center_mem C, ?_⟩
  change RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart C x ∈ q.source
  rw [RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_center]
  exact hx

theorem nativeFamilyBallChart_mapsTo {V : Set Geometry.ComplexBall.PrescribedSignsB.BallChart} (hq : Set.MapsTo q q.source V) :
    Set.MapsTo (nativeFamilyBallChart C q) (nativeFamilyBallChart C q).source V :=
  fun _ hy => hq hy.2

variable [IsIntegral S.left] [Smooth S.hom]

theorem nativeFamilyBallChart_holomorphic
    (hq : DifferentiableOn ℂ q q.source) (hi : DifferentiableOn ℂ q.symm q.target) :
    (nativeFamilyBallChart C q).MDifferentiable
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ)) (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) := by
  have hqd : q.MDifferentiable (𝓘(ℂ, RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (𝓘(ℂ, Geometry.ComplexBall.PrescribedSignsB.BallChart)) :=
    ⟨mdifferentiableOn_iff_differentiableOn.mpr hq, mdifferentiableOn_iff_differentiableOn.mpr hi⟩
  exact (RepresentationTheory.Theta.Geometric.Family.IntrinsicChart.familyNativeChart_holomorphic C).trans hqd

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallChart
