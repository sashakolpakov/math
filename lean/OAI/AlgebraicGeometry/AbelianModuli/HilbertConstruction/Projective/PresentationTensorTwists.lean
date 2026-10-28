import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationCohomologyPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TensorPowers

/-! # Presentation Tensor Twists -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwists.ClosedProjectiveEmbedding

noncomputable section

/-! The homogeneous presentation identifies tensoring by powers of the restricted hyperplane bundle with the actual coordinate twists. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def tensorTwistPullbackIso {R : Type u} [CommRing R] {n : ℕ} {X : Over (Spec (.of R))}
    (i : X ⟶ ProjectivePresentations.affineProjectiveSpace R n) [IsClosedImmersion i.left]
    (M : X.left.Modules) (d : ℕ) :
    (Scheme.Modules.pullback (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left).obj
      (Tensor.ProductSheaf.tensorModule M (((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left).tensorPower d).sheaf) ≅
    Tensor.ProductSheaf.tensorModule ((Scheme.Modules.pullback (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left).obj M)
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) d).sheaf := by
  let L := (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback i.left
  have : IsIso (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left := (Over.forget _).map_isIso (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom
  exact Tensor.ProductBaseChange.tensorModulePullbackIso (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left M (L.tensorPower d).sheaf ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (Iso.refl _) (L.powerBaseChangeIso (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.presentation i).hom.left d ≪≫
      (TensorPower.Maps.tensorPowerFunctor _ d).mapIso (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.twistingIso i) ≪≫
      ProjectiveTwisting.TensorPowers.projectiveTwistingBundle_tensorPowerIso (Closed.ProjectiveHomogeneousPresentation.ClosedProjectiveEmbedding.ideal i) d)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwists.ClosedProjectiveEmbedding
