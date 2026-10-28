import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeProjectiveEquations
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroCharts

/-! # Relative Chart Equations -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeChartEquations.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! The actual varying-family Picard zero chart over a local base is
the closed quotient by a constructed list of equations. Its length is
exactly the closed fiber's original first coherent cohomology dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme} {A B T : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    [IsAffine T.left] [IsLocalRing Γ(T.left, ⊤)] [IsNoetherianRing Γ(T.left, ⊤)]
    [IsLocallyNoetherian T.left] (a : T ⟶ B)

theorem exists_zeroChart_equations
    (eM : (Scheme.Modules.pullback ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι
      (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint T.left))).obj (D.line a).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint T.left))) :
    ∃ (n : ℕ) (v : Fin n → Γ(T.left, ⊤)),
      n = RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1 (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
        (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (D.line a) ∧
      Ideal.span (Set.range v) ≤ IsLocalRing.maximalIdeal Γ(T.left, ⊤) ∧
      Nonempty (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a ≅ RepresentationTheory.Theta.Geometric.Affine.QuotientPoints.affineQuotientScheme T.left (Ideal.span (Set.range v))) := by
  let : IsProper (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.fst T.hom A.hom))
  let : Smooth (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.fst T.hom A.hom))
  let : GeometricallyConnected (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.fst T.hom A.hom))
  exact RelativeProjectiveEquations.Geometric.exists_relativeProjective_frame_equations (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
    (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis T) (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis_section T)
    (D.line a) (D.frame a) eM
    (FormalGeometry.Completion.Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T)
      (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (D.line a))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeChartEquations.Geometric.RelativeRigidifiedCharts
