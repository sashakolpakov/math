import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.ProjectiveSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBaseChange

/-! # Presentation Tensor Twisting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! The O(1) bundle of the existing native product presentation is the
external tensor product of the two embedding bundles. This formula and
the actual presentation base change are compatible over every base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {S T : Scheme.{u}} {X Y : Over S}
variable (P : ProjectivePresentations.ProjectivePresentation X) (Q : ProjectivePresentations.ProjectivePresentation Y)

def ProjectivePresentations.ProjectivePresentation.productTwistingBundleIso :
    (P.product Q).ampleLineBundle.sheaf ≅ (Graph.ExternalTensorBundle.externalTensorBundle P.ampleLineBundle Q.ampleLineBundle).sheaf :=
  (P.canonicalSectionData.product Q.canonicalSectionData).twistingIso

def ProjectivePresentations.ProjectivePresentation.baseChangeTwistingBundleIso (f : T ⟶ S) :
    (P.baseChange f).ampleLineBundle.sheaf ≅
      (P.ampleLineBundle.pullback (CategoryTheory.Limits.pullback.fst X.hom f)).sheaf :=
  (P.canonicalSectionData.baseChange f).twistingIso

def ProjectivePresentations.ProjectivePresentation.graphTwistingBundleIso [IsSeparated Y.hom] (p : X ⟶ Y) :
    (P.graph Q p).ampleLineBundle.sheaf ≅
      (P.ampleLineBundle.tensor (Q.ampleLineBundle.pullback p.left)).sheaf :=
  (P.canonicalSectionData.graph Q.canonicalSectionData p).twistingIso

def ProjectivePresentations.ProjectivePresentation.productBaseChangeTwistingBundleIso (f : T ⟶ S) :
    ((P.baseChange f).product (Q.baseChange f)).ampleLineBundle.sheaf ≅
      ((P.product Q).ampleLineBundle.pullback (Graph.FamilyNaturality.overProductBaseChangeMap f X Y)).sheaf := by
  let X' := (Over.pullback f).obj X
  let Y' := (Over.pullback f).obj Y
  let L := P.ampleLineBundle
  let M := Q.ampleLineBundle
  exact (P.baseChange f).productTwistingBundleIso (Q.baseChange f) ≪≫
    Tensor.Bifunctor.tensorModuleMapIso
      ((Scheme.Modules.pullback (fst X' Y').left).mapIso (P.baseChangeTwistingBundleIso f))
      ((Scheme.Modules.pullback (snd X' Y').left).mapIso (Q.baseChangeTwistingBundleIso f)) ≪≫
    (External.TensorBaseChange.externalTensorBundle_baseChangeIso f L M).symm ≪≫
      (Scheme.Modules.pullback (Graph.FamilyNaturality.overProductBaseChangeMap f X Y)).mapIso (P.productTwistingBundleIso Q).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
