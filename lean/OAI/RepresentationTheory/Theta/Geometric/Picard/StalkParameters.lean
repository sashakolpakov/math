import OAI.RepresentationTheory.Theta.Geometric.Picard.ZeroFiberTriviality
import OAI.RepresentationTheory.Theta.Geometric.SpecClosedPoint

/-! # Stalk Parameters -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.StalkParameters

noncomputable section

/-! Actual parameter localizations and their closed-fiber trivializations
at points of the Picard comparison scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

def picardStalkParameter {K : Type u} [Field K] (B : Over (Spec (.of K))) (b : B.left) :
    Over (Spec (.of K)) := Over.mk (B.left.fromSpecStalk b ≫ B.hom)

def picardStalkMap {K : Type u} [Field K] (B : Over (Spec (.of K))) (b : B.left) :
    picardStalkParameter B b ⟶ B := Over.homMk (B.left.fromSpecStalk b) rfl

instance picardStalkParameter_isAffine {K : Type u} [Field K]
    (B : Over (Spec (.of K))) (b : B.left) : IsAffine (picardStalkParameter B b).left :=
  inferInstanceAs (IsAffine (Spec (B.left.presheaf.stalk b)))

instance picardStalkParameter_isLocalRing {K : Type u} [Field K]
    (B : Over (Spec (.of K))) (b : B.left) :
    IsLocalRing Γ((picardStalkParameter B b).left, ⊤) :=
  SpecLocalRings.specGlobal_isLocalRing (B.left.presheaf.stalk b)

instance picardStalkParameter_isNoetherianRing {K : Type u} [Field K]
    (B : Over (Spec (.of K))) [IsLocallyNoetherian B.left] (b : B.left) :
    IsNoetherianRing Γ((picardStalkParameter B b).left, ⊤) :=
  SpecLocalRings.specGlobal_isNoetherianRing (B.left.presheaf.stalk b)

theorem picardStalkMap_closedPoint {K : Type u} [Field K]
    (B : Over (Spec (.of K))) (b : B.left) :
    (picardStalkMap B b).left (Local.AxisCechChart.affineLocalClosedPoint (picardStalkParameter B b).left) = b := by
  have : IsLocalRing Γ(Spec (B.left.presheaf.stalk b), ⊤) :=
    SpecLocalRings.specGlobal_isLocalRing (B.left.presheaf.stalk b)
  change B.left.fromSpecStalk b (Local.AxisCechChart.affineLocalClosedPoint (Spec (B.left.presheaf.stalk b))) = b
  rw [SpecClosedPoint.affineLocalClosedPoint_spec]
  exact Scheme.fromSpecStalk_closedPoint

theorem picardStalk_fiber_trivial
    {K : Type u} [Field K] [IsAlgClosed K] {A B : Over (Spec (.of K))}
    [GrpObj A] [IsCommMonObj A] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    [IsLocallyNoetherian B.left] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A B) (z : D.zeroScheme.left) :
    Nonempty ((Scheme.Modules.pullback
      ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (picardStalkParameter B (D.zeroScheme.hom z))).hom.fiberι
        (Local.AxisCechChart.affineLocalClosedPoint (picardStalkParameter B (D.zeroScheme.hom z)).left))).obj
      (D.line (picardStalkMap B (D.zeroScheme.hom z))).sheaf ≅
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (picardStalkParameter B (D.zeroScheme.hom z))).hom.fiber
        (Local.AxisCechChart.affineLocalClosedPoint (picardStalkParameter B (D.zeroScheme.hom z)).left))) :=
  ZeroFiberTriviality.picard_zeroScheme_fiber_trivial D _ _ z (picardStalkMap_closedPoint B _)

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.StalkParameters
