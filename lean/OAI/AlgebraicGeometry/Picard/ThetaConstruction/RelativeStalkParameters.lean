import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiberTriviality
import OAI.RepresentationTheory.Theta.Geometric.SpecClosedPoint

/-! # Relative Stalk Parameters -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! Literal stalk parameters of the original varying Picard zero
scheme, with their actual closed points and fiber trivializations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.SpecClosedPoint

variable {S : Scheme}

def stalkParameter (B : Over S) (b : B.left) : Over S :=
  Over.mk (B.left.fromSpecStalk b ≫ B.hom)

def stalkMap (B : Over S) (b : B.left) : stalkParameter B b ⟶ B :=
  Over.homMk (B.left.fromSpecStalk b) rfl

instance stalkParameter_isAffine (B : Over S) (b : B.left) : IsAffine (stalkParameter B b).left :=
  inferInstanceAs (IsAffine (Spec (B.left.presheaf.stalk b)))

instance stalkParameter_isLocalRing (B : Over S) (b : B.left) :
    IsLocalRing Γ((stalkParameter B b).left, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isLocalRing (B.left.presheaf.stalk b)

instance stalkParameter_isNoetherianRing (B : Over S) [IsLocallyNoetherian B.left] (b : B.left) :
    IsNoetherianRing Γ((stalkParameter B b).left, ⊤) := RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isNoetherianRing (B.left.presheaf.stalk b)

instance stalkParameter_isLocallyNoetherian (B : Over S) [IsLocallyNoetherian B.left] (b : B.left) :
    IsLocallyNoetherian (stalkParameter B b).left :=
  inferInstanceAs (IsLocallyNoetherian (Spec (B.left.presheaf.stalk b)))

theorem stalkMap_closedPoint (B : Over S) (b : B.left) :
    (stalkMap B b).left (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint (stalkParameter B b).left) = b := by
  let : IsLocalRing Γ(Spec (B.left.presheaf.stalk b), ⊤) :=
    RepresentationTheory.Theta.Geometric.SpecLocalRings.specGlobal_isLocalRing (B.left.presheaf.stalk b)
  change B.left.fromSpecStalk b (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint (Spec (B.left.presheaf.stalk b))) = b
  rw [RepresentationTheory.Theta.Geometric.SpecClosedPoint.affineLocalClosedPoint_spec]
  exact Scheme.fromSpecStalk_closedPoint

theorem stalk_fiber_trivial {A B : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    (z : (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).left) :
    Nonempty ((Scheme.Modules.pullback
      ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))).hom.fiberι
        (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint (stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z)).left))).obj
      (D.line (stalkMap B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))).hom.fiber
        (RepresentationTheory.Theta.Geometric.Local.AxisCechChart.affineLocalClosedPoint (stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z)).left))) :=
  RelativeFiberTriviality.Geometric.RelativeRigidifiedCharts.zeroScheme_fiber_trivial P D _ _ z (stalkMap_closedPoint B _)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkParameters.Geometric.RelativeRigidifiedCharts
