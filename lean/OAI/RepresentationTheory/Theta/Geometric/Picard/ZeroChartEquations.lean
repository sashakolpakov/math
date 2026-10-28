import OAI.RepresentationTheory.Theta.Geometric.Projective.PicardLocalEquations
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductZeroChart

/-! # Zero Chart Equations -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroChartEquations

noncomputable section

/-! The actual Picard zero chart over a local parameter scheme is a
closed quotient with precisely the closed fiber's H1 number of equations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A B T : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)
    [IsAffine T.left] [IsLocalRing Γ(T.left, ⊤)] [IsNoetherianRing Γ(T.left, ⊤)]
    (a : T ⟶ B)

theorem exists_picard_zeroChart_equations
    (eM : (Scheme.Modules.pullback ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι
      (Local.AxisCechChart.affineLocalClosedPoint T.left))).obj (D.line a).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber (Local.AxisCechChart.affineLocalClosedPoint T.left))) :
    ∃ (n : ℕ) (v : Fin n → Γ(T.left, ⊤)),
      n = Projective.PicardLocalEquations.projectiveClosedFiberH1 (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
        (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a) ∧
      Ideal.span (Set.range v) ≤ IsLocalRing.maximalIdeal Γ(T.left, ⊤) ∧
      Nonempty (D.zeroChart a ≅ Affine.QuotientPoints.affineQuotientScheme T.left (Ideal.span (Set.range v))) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom := (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T).proper
  exact Projective.PicardLocalEquations.exists_projective_frame_equations A.hom (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
    (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (snd T A).left T.hom
    (IsPullback.of_hasPullback T.hom A.hom).flip (AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Chart.Construction.polarizationFamilyAxis A)
    (AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Chart.Construction.polarizationFamilyAxis_section A) (D.line a) (D.frame a) eM
    (AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T)
      (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a))

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroChartEquations
