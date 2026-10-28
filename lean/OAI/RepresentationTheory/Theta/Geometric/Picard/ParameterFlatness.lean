import OAI.RepresentationTheory.Theta.Geometric.AbelianPicardProjectionFlatness
import OAI.RepresentationTheory.Theta.Geometric.Picard.ComparisonUnramified
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Parameter Flatness -/

namespace OAI.RepresentationTheory.Theta.Geometric.Picard.ParameterFlatness

noncomputable section

/-! The actual parameter comparison with an arbitrary rigidified family
is flat once its universally injective parameter space has the H1 dimension. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem abelian_picardParameterProjection_flat (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    [IsProper A.toOver.hom] [Smooth A.toOver.hom] [GeometricallyIntegral A.toOver.hom]
    {n : ℕ} (N : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme n AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    [IsLocallyNoetherian (N.scheme ⊗ T).left]
    (Q : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver N.scheme) (L : AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine A.toOver T)
    (hQ : ∀ U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase, Function.Injective (Q.relativeValue (T := U)))
    (hH1 : letI := AlgebraicGeometry.SheafCohomology.Scalars.Projective.zariskiComplexCohomologyModule A (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1
      Module.finrank ℂ (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.carrier) 1) ≤ n) :
    Flat (ParameterComparison.picardParameterProjection Q L).left := by
  let D := RigidifiedPicardDifference.rigidifiedPicardDifference (RigidifiedParameterPullback.rigidifiedParameterPullback Q (fst N.scheme T))
    (RigidifiedParameterPullback.rigidifiedParameterPullback L (snd N.scheme T))
  have : SmoothOfRelativeDimension n (snd N.scheme T).left :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
      (IsPullback.of_hasPullback N.scheme.hom T.hom) N.smoothDimension
  have : Mono (ParameterComparison.picardParameterProjection Q L) := ParameterComparison.picardParameterProjection_mono Q L hQ
  have : Mono (D.zeroScheme.hom ≫ (snd N.scheme T).left) :=
    Over.mono_left_of_mono (ParameterComparison.picardParameterProjection Q L)
  exact AbelianPicardProjectionFlatness.abelian_picard_zero_projection_flat A D n (snd N.scheme T).left hH1

end

end OAI.RepresentationTheory.Theta.Geometric.Picard.ParameterFlatness
