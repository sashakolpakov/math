import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.ProjectiveSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoefficientSectionBasis

/-! # Presentation Source Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Complete presentation section data pull back through an isomorphism
over the base, with the actual coefficient basis and sections retained. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {X Y : Over S} {P : Projective.ProjectivePresentations.ProjectivePresentation Y}
variable {L : Line.Bundles.LineBundle Y.left} {D : P.SectionData L}

local instance Projective.ProjectivePresentations.ProjectivePresentation.SectionData.sourceTransportClosedImmersion (e : X ≅ Y) : IsClosedImmersion e.hom.left :=
  Grassmann.ProjectivePresentation.overIso_closedImmersion e

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData.precompIso (C : D.CompleteData) (e : X ≅ Y) :
    (D.precomp e.hom).CompleteData where
  basis := C.basis.map (IsoCoefficientSectionBasis.sourceIsoCoefficientSectionEquiv e L.sheaf)
  sections_eq := by
    funext i
    change Ample.LineBundles.pullbackSection e.hom.left (D.sections i) = _
    exact (congrArg (Ample.LineBundles.pullbackSection e.hom.left) (congrFun C.sections_eq i)).trans
      (IsoCoefficientSectionBasis.coefficientRingBasisFamily_sourceIso e L.sheaf C.basis i).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
