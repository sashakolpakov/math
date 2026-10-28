import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.GraphIsoTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.External.TensorBundleNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphTwistingInvariance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphIsomorphismTransport

/-! # Graph Bundle Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GraphBundleTransport

noncomputable section

/-! Isomorphisms of source and target families preserving their embedding
line bundles transport the full native product-graph Hilbert condition.
The chosen embeddings need not have the same ambient dimensions. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {X X' Y Y' : Over S}
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
variable [Flat X'.hom] [LocallyOfFinitePresentation X'.hom] [IsSeparated Y'.hom]
variable (P : ProjectivePresentations.ProjectivePresentation X) (Q : ProjectivePresentations.ProjectivePresentation Y)
variable (P' : ProjectivePresentations.ProjectivePresentation X') (Q' : ProjectivePresentations.ProjectivePresentation Y')
variable (e : X ≅ X') (d : Y ≅ Y')
variable (eL : (P'.ampleLineBundle.pullback e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
variable (eM : (Q'.ampleLineBundle.pullback d.hom.left).sheaf ≅ Q.ampleLineBundle.sheaf)

include P Q P' Q' e d eL eM in
private abbrev graphProductBundleComparison :=
  (Scheme.Modules.pullbackComp (tensorIso e d).hom.left
    (P'.product Q').embedding.left).symm.app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S (P'.product Q').dimension).sheaf ≪≫
    (Scheme.Modules.pullback (tensorIso e d).hom.left).mapIso
      (P'.productTwistingBundleIso Q') ≪≫
    External.TensorBundleNaturality.externalTensorBundle_pullback_product e.hom d.hom P'.ampleLineBundle Q'.ampleLineBundle ≪≫
      External.TensorBundleNaturality.externalTensorBundle_congr eL eM ≪≫ (P.productTwistingBundleIso Q).symm

include P Q P' Q' e d eL eM in
private abbrev graphProductTwistingEquivalence (R : Polynomial ℚ) (p : X ⟶ Y) := by
  let c : X ⊗ Y ≅ X' ⊗ Y' := tensorIso e d
  let j := c.hom ≫ (P'.product Q').embedding
  let : IsClosedImmersion j.left :=
    @IsClosedImmersion.comp _ _ _ _ _ (Grassmann.ProjectivePresentation.overIso_closedImmersion c) (P'.product Q').closedImmersion
  exact Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.iff_of_twistingIso
    (P.product Q).embedding j (graphProductBundleComparison P Q P' Q' e d eL eM).symm R p

include eL eM in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.graphHilbertPolynomial_transport_of_bundleIso
    (R : Polynomial ℚ) (p : X ⟶ Y) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (P.product Q).embedding R p ↔
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (P'.product Q').embedding R
        (CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap e d p) := by
  exact (graphProductTwistingEquivalence P Q P' Q' e d eL eM R p).trans
    (Product.GraphIsoTransport.productGraphIsoTransport e d (P'.product Q').embedding R p)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GraphBundleTransport
