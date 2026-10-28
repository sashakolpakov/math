import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveHomogeneousPresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.SectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LineBundleSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers

/-! # Projective Twisting Sections Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveTwistingSectionsFinite.ClosedProjectiveEmbedding

noncomputable section

/-! Nonnegative twisting powers on every closed projective subscheme over a Noetherian ring have finite modules of actual sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable {X : Over (Spec (.of R))} (i : X ⟶ Projective.ProjectivePresentations.affineProjectiveSpace R n)
variable [IsClosedImmersion i.left]

theorem twistingPowerSections_finite (d : ℕ) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj
      (((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left).tensorPower d).sheaf) := by
  have : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
      (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i)).hom).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) d).sheaf) :=
    ProjectiveTwisting.SectionsFinite.projectiveTwistingSections_finite (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) d
  have hf : Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor
      (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i)).hom).obj
      ((ProjectiveTwisting.Bundle.projectiveTwistingBundle (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) 1).tensorPower d).sheaf) :=
    Module.Finite.equiv (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsIso
      (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i)).hom
      (ProjectiveTwisting.TensorPowers.projectiveTwistingBundle_tensorPowerIso (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) d)).symm
  exact @Module.Finite.equiv R _ _ _ _ _ _ _ hf
    (Intrinsic.LineBundleSections.lineBundlePowerSectionsOverIso (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i)
      ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left)
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) 1) (ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.twistingIso i) d).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ProjectiveTwistingSectionsFinite.ClosedProjectiveEmbedding
