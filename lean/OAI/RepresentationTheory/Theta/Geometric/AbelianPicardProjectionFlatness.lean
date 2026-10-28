import OAI.RepresentationTheory.Theta.Geometric.Picard.StalkFlatness
import OAI.RepresentationTheory.Theta.Geometric.AbelianFiberDimension

/-! # Abelian Picard Projection Flatness -/

namespace OAI.RepresentationTheory.Theta.Geometric.AbelianPicardProjectionFlatness

noncomputable section

/-! An algebraic structure-sheaf H1 bound proves flatness of the actual
Picard zero projection inside a smooth parameter space. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem abelian_picard_zero_projection_flat (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [IsProper A.toOver.hom] [Smooth A.toOver.hom] [GeometricallyIntegral A.toOver.hom]
    {B : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsLocallyNoetherian B.left] (D : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver B)
    {Y : Scheme.{0}} (n : ℕ) (p : B.left ⟶ Y) [SmoothOfRelativeDimension n p]
    [Mono (D.zeroScheme.hom ≫ p)]
    (hH1 : letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) ≤ n) :
    Flat (D.zeroScheme.hom ≫ p) := by
  let := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
  apply FlatSourceLocalizations.flat_of_ambient_stalk_localizations
  intro z
  apply Picard.StalkFlatness.picard_zeroScheme_stalk_projection_flat D n p z
  let T := Picard.StalkParameters.picardStalkParameter B (D.zeroScheme.hom z)
  let a := Picard.StalkParameters.picardStalkMap B (D.zeroScheme.hom z)
  obtain ⟨eM⟩ := Picard.StalkParameters.picardStalk_fiber_trivial D z
  have h := AbelianFiberDimension.projectiveClosedFiberH1_eq_abelianH1 A (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.tensorFamilyOver A.toOver T).hom
    (AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily.Construction.geometricGroupFamilyProjectivePresentation A.toOver T)
    (snd T A.toOver).left T.hom (IsPullback.of_hasPullback T.hom A.toOver.hom).flip (D.line a) eM
  exact h.le.trans hH1

end

end OAI.RepresentationTheory.Theta.Geometric.AbelianPicardProjectionFlatness
