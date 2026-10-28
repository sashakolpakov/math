import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeChartEquations
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroScheme
import OAI.RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints

/-! # Relative Local Equations -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalEquations.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! The constructed equations describe the actual pullback of the
varying-family Picard zero scheme, by its all-test classification. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints

variable {S : Scheme} {A B T : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [IsLocallyNoetherian T.left]
    (a : T ⟶ B)

def zeroSchemeLocalChartIso : RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P) a.left ≅ RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a := by
  apply RepresentationTheory.Theta.Geometric.Affine.TestMonomorphisms.monoIsoOfAffineTests
  intro U _
  let V := Over.mk (U.hom ≫ T.hom)
  let j : V ⟶ T := Over.homMk U.hom rfl
  exact (RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback_hasLift_iff (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P) a.left U).trans
    ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme_hasLift_iff D P (j ≫ a)).trans
      (RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts.zeroChart_hasLift_iff_relative_zero D P a j).symm)

theorem exists_zeroScheme_local_equations [IsLocalRing Γ(T.left, ⊤)]
    (eM : (Scheme.Modules.pullback ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι
      (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint T.left))).obj (D.line a).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint T.left))) :
    ∃ (n : ℕ) (v : Fin n → Γ(T.left, ⊤)),
      n = RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1 (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
        (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (D.line a) ∧
      Ideal.span (Set.range v) ≤ IsLocalRing.maximalIdeal Γ(T.left, ⊤) ∧
      Nonempty (RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints.subobjectPullback (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P) a.left ≅
        RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme T.left (Ideal.span (Set.range v))) := by
  obtain ⟨n, v, hn, hv, ⟨e⟩⟩ := RelativeChartEquations.Geometric.RelativeRigidifiedCharts.exists_zeroChart_equations P D a eM
  exact ⟨n, v, hn, hv, ⟨zeroSchemeLocalChartIso P D a ≪≫ e⟩⟩

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeLocalEquations.Geometric.RelativeRigidifiedCharts
