import OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericFiberLineTriviality
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiberTriviality

/-! # Generic Zero Lift -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericZeroLift.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! An actual Picard-zero point over the generic point of an integral
local test extends to that whole original test. The extension is
constructed from generic-fiber line triviality and the represented
original Picard zero functor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme} {A B T : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A)
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    [IsAffine T.left] [IsLocalRing Γ(T.left, ⊤)] [IsNoetherianRing Γ(T.left, ⊤)]
    [IsLocallyNoetherian T.left] [IsIntegral T.left]

theorem zeroScheme_generic_lift (a : T ⟶ B) (z : (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).left)
    (h : a.left (genericPoint T.left) = (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z) :
    ∃ w : T ⟶ RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroSchemeOver D P, w ≫ RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion D P = a := by
  let π := (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A T).hom
  let : IsProper π := inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.fst T.hom A.hom))
  let : Smooth π := inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.fst T.hom A.hom))
  let : GeometricallyConnected π :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.fst T.hom A.hom))
  have hη := RelativeFiberTriviality.Geometric.RelativeRigidifiedCharts.zeroScheme_fiber_trivial P D a (genericPoint T.left) z h
  obtain ⟨e⟩ := GenericFiberLineTriviality.Geometric.genericFiber_line_trivial π (D.line a)
    (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A T P) (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis T) (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.axis_section T) (D.frame a) hη
  apply (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroInclusion_factorization D P T a).mp
  exact congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T)) (Quotient.sound ⟨e⟩)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.GenericZeroLift.Geometric.RelativeRigidifiedCharts
