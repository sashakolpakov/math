import OAI.RepresentationTheory.Theta.Geometric.Family.ChartOpenImage

/-! # Fixed Family Base Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates

noncomputable section

/-! Every actual family chart has the original function-field
dimension and hence admits coordinates in the same fixed finite model. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

def fixedFamilyBaseCoordinates {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom] {g : ℕ}
    {G : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S.left} {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    (C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts G x) :
    (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom) → ℂ) ≃L[ℂ] Intrinsic.FamilyFrames.FamilyChartBase C :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_pi, Fintype.card_fin]
    exact C.dimension.symm)

end

end OAI.RepresentationTheory.Theta.Geometric.FixedFamilyBaseCoordinates
