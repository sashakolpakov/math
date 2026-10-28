import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeStalkFlatness
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Relative Etale Criterion -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeEtaleCriterion.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! Constructed local equations prove flatness, and hence etaleness,
of the actual varying-family Picard zero projection when its first
cohomology bounds fit the smooth ambient relative dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {S : Scheme} {A B : Over S} [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [IsLocallyNoetherian B.left] (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)
    {Y : Scheme} (n : ℕ) (p : B.left ⟶ Y) [SmoothOfRelativeDimension n p]
    [FormallyUnramified ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p)]

theorem zeroProjection_flat
    (hdim : ∀ z : (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).left,
      RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1
        (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))).hom
        (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z)) P)
        (D.line (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))) ≤ n) :
    Flat ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p) :=
  RepresentationTheory.Theta.Geometric.FlatSourceLocalizations.flat_of_ambient_stalk_localizations (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom p
    (fun z => RelativeStalkFlatness.Geometric.RelativeRigidifiedCharts.stalk_projection_flat P D n p z (hdim z))

theorem zeroProjection_etale [IsLocallyNoetherian Y]
    (hdim : ∀ z : (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).left,
      RelativeProjectiveEquations.Geometric.relativeProjectiveClosedFiberH1
        (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))).hom
        (FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyProjectivePresentation A (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkParameter B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z)) P)
        (D.line (RelativeStalkParameters.Geometric.RelativeRigidifiedCharts.stalkMap B ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom z))) ≤ n) :
    Etale ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p) := by
  let : Flat ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p) := zeroProjection_flat P D n p hdim
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  let : LocallyOfFiniteType (RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom := RelativeFiniteType.Geometric.RelativeRigidifiedCharts.zeroScheme_locallyOfFiniteType P D
  let : LocallyOfFiniteType ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p) := inferInstance
  let : LocallyOfFinitePresentation ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p) := inferInstance
  exact Etale.of_formallyUnramified_of_flat ((RelativeZeroScheme.Geometric.RelativeRigidifiedCharts.zeroScheme D P).hom ≫ p)

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeEtaleCriterion.Geometric.RelativeRigidifiedCharts
