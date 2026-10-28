import OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroChartEquations
import OAI.RepresentationTheory.Theta.Geometric.SubobjectPullbackPoints
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductZeroScheme

/-! # Zero Scheme Local Equations -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroSchemeLocalEquations

noncomputable section

/-! The local quotient equations describe the actual base change of
the Picard zero scheme, via its classification on all test schemes. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
    {A B T : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian B.left] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B)
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] (a : T ⟶ B)

def picardZeroSchemeLocalChartIso : SubobjectPullbackPoints.subobjectPullback D.zeroScheme a.left ≅ D.zeroChart a := by
  apply Affine.TestMonomorphisms.monoIsoOfAffineTests
  intro U _
  let V := Over.mk (U.hom ≫ T.hom)
  let j : V ⟶ T := Over.homMk U.hom rfl
  exact (SubobjectPullbackPoints.subobjectPullback_hasLift_iff D.zeroScheme a.left U).trans
    ((D.zeroScheme_hasLift_iff (j ≫ a)).trans (D.zeroChart_hasLift_iff_relative_zero a j).symm)

theorem exists_picard_zeroScheme_local_equations [IsLocalRing Γ(T.left, ⊤)]
    (eM : (Scheme.Modules.pullback ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiberι
      (Local.AxisCechChart.affineLocalClosedPoint T.left))).obj (D.line a).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom.fiber (Local.AxisCechChart.affineLocalClosedPoint T.left))) :
    ∃ (n : ℕ) (v : Fin n → Γ(T.left, ⊤)),
      n = Projective.PicardLocalEquations.projectiveClosedFiberH1 (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
        (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A T) (D.line a) ∧
      Ideal.span (Set.range v) ≤ IsLocalRing.maximalIdeal Γ(T.left, ⊤) ∧
      Nonempty (SubobjectPullbackPoints.subobjectPullback D.zeroScheme a.left ≅
        Affine.QuotientPoints.affineQuotientScheme T.left (Ideal.span (Set.range v))) := by
  obtain ⟨n, v, hn, hv, ⟨e⟩⟩ := ZeroChartEquations.exists_picard_zeroChart_equations D a eM
  exact ⟨n, v, hn, hv, ⟨picardZeroSchemeLocalChartIso D a ≪≫ e⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroSchemeLocalEquations
