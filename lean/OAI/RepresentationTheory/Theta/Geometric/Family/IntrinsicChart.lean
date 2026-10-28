import OAI.RepresentationTheory.Theta.Geometric.Affine.ParameterHolomorphic
import OAI.RepresentationTheory.Theta.Geometric.ManifoldChartInverse

/-! # Intrinsic Chart -/

namespace OAI.RepresentationTheory.Theta.Geometric.Family.IntrinsicChart

noncomputable section

/-! The original family base chart is a genuine holomorphic chart of the
native scheme manifold, with holomorphic inverse and bijective derivatives. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Manifold

variable {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g : ℕ} {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left}
  {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x)

def familyNativeChart : OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (Intrinsic.FamilyFrames.FamilyChartBase C) :=
  C.charts.charts.charts.base.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap C.algebra C.openMap)

theorem familyNativeChart_symm_apply (z : Intrinsic.FamilyFrames.FamilyChartBase C) :
    (familyNativeChart C).symm z = Intrinsic.FamilyFrames.familyChartParameter C z := rfl

theorem familyNativeChart_center_mem : x ∈ (familyNativeChart C).source := by
  have hp : C.point ∈ C.charts.charts.charts.base.source := by
    simpa only [AlgHom.comp_assoc, C.charts.retraction, AlgHom.comp_id] using C.charts.charts.charts.basePoint
  exact ⟨C.point, hp, C.center⟩

theorem familyNativeChart_center : familyNativeChart C x = Intrinsic.FamilyFrames.familyChartCenter C := by
  calc
    familyNativeChart C x = familyNativeChart C (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra C.openMap C.point) :=
      congrArg (familyNativeChart C) C.center.symm
    _ = Intrinsic.FamilyFrames.familyChartCenter C := OpenPartialHomeomorph.lift_openEmbedding_apply _ _

variable [IsIntegral S.left] [Smooth S.hom]

theorem familyNativeChart_holomorphic :
    (familyNativeChart C).MDifferentiable
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
      (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartBase C)) := by
  have hi : MDifferentiableOn (𝓘(ℂ, Intrinsic.FamilyFrames.FamilyChartBase C))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ))
      (familyNativeChart C).symm (familyNativeChart C).target := by
    intro z hz
    exact (Affine.ParameterHolomorphic.affineParameter_holomorphic C.algebra C.openMap C.charts.charts.charts.base
      C.charts.charts.charts.regularBase hz).mdifferentiableWithinAt
  refine ⟨?_, hi⟩
  intro y hy
  apply (ManifoldChartInverse.manifoldChart_holomorphic_of_inverse ?_ (familyNativeChart C) hi hy).mdifferentiableWithinAt
  simpa only [Module.finrank_fin_fun] using C.dimension

end

end OAI.RepresentationTheory.Theta.Geometric.Family.IntrinsicChart
