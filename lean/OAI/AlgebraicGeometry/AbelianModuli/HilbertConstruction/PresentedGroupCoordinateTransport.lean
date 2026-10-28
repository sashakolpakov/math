import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentedGroupGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GraphBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.LinearCoordinateChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.ProjectiveSectionData

/-! # Presented Group Coordinate Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual linear changes of ambient projective coordinates preserve
the original bounded multiplication and inversion graph conditions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance PresentedGroupCoordinateTransport.coordinateGroupProductFlat {S : Scheme.{u}}
    (X Y : Over S) [Flat X.hom] [Flat Y.hom] : Flat (X ⊗ Y).hom :=
  inferInstanceAs (Flat (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

local instance PresentedGroupCoordinateTransport.coordinateGroupProductFinitePresentation {S : Scheme.{u}}
    (X Y : Over S) [LocallyOfFinitePresentation X.hom] [LocallyOfFinitePresentation Y.hom] :
    LocallyOfFinitePresentation (X ⊗ Y).hom :=
  inferInstanceAs (LocallyOfFinitePresentation
    (CategoryTheory.Limits.pullback.fst X.hom Y.hom ≫ X.hom))

/-- An isomorphism preserving the embedding line bundle transports both graph bounds. -/
theorem FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofBundleIso
    {S : Scheme.{u}} {X Y : Over S}
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
    [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y) (e : X ≅ Y)
    (eL : (Q.ampleLineBundle.pullback e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (Pm Pi : Polynomial ℚ)
    (hD : D.ProjectiveGraphBounds P Pm Pi) :
    (D.ofIso e).ProjectiveGraphBounds Q Pm Pi := by
  let e₂ : ((Q.product Q).ampleLineBundle.pullback (tensorIso e e).hom.left).sheaf ≅
      (P.product P).ampleLineBundle.sheaf :=
    (Scheme.Modules.pullback (tensorIso e e).hom.left).mapIso (Q.productTwistingBundleIso Q) ≪≫
      External.TensorBundleNaturality.externalTensorBundle_pullback_product e.hom e.hom Q.ampleLineBundle Q.ampleLineBundle ≪≫
        External.TensorBundleNaturality.externalTensorBundle_congr eL eL ≪≫ (P.productTwistingBundleIso P).symm
  constructor
  · exact ((P.product P).graphHilbertPolynomial_transport_of_bundleIso P
      (Q.product Q) Q (tensorIso e e) e e₂ eL Pm D.mul).mp hD.1
  · exact (P.graphHilbertPolynomial_transport_of_bundleIso P Q Q e e eL eL Pi D.inv).mp hD.2

variable {S : Scheme.{u}} {X Y : Over S} {n : ℕ}
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    (e : X ≅ Y)
    (z : (Fin (n + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (n + 1) →₀ Γ(S, ⊤)))
    (h : e.hom ≫ j = i ≫ (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z).hom)

/-- The needed O(1) isomorphism is constructed from the coordinate map. -/
def PresentedGroupCoordinateTransport.projectiveEmbeddingCoordinateTwistingIso :
    ((((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback j.left).pullback e.hom.left).sheaf) ≅
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback i.left).sheaf := by
  let P : Projective.ProjectivePresentations.ProjectivePresentation X := ⟨n, i, inferInstance⟩
  let a := Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso n S z
  let Q : Projective.ProjectivePresentations.ProjectivePresentation X := {
    dimension := n
    embedding := i ≫ a.hom
    closedImmersion := @IsClosedImmersion.comp _ _ _ _ _
      (inferInstanceAs (IsClosedImmersion i.left)) (Grassmann.ProjectivePresentation.overIso_closedImmersion a) }
  let C := P.canonicalSectionData
  let hs := GeneratingSectionFrameChanges.transformSectionFamily_covers X.hom.appTop.hom P.ampleLineBundle C.sections C.covers
    z.symm.toLinearMap z.symm.surjective
  let D : Q.SectionData P.ampleLineBundle := {
    sections := Section.CoefficientTransformations.transformSectionFamily X.hom.appTop.hom P.ampleLineBundle.sheaf
      C.sections z.symm.toLinearMap
    covers := hs
    embedding_eq := (congrArg (fun f => f ≫ a.hom) C.embedding_eq).trans
      (Relative.SectionLinearCoordinateAction.sectionProjectiveMorphism_linearCoordinateIso X.hom C.sections C.covers z hs) }
  exact (Scheme.Modules.pullbackComp e.hom.left j.left).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app
      (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).sheaf ≪≫ D.twistingIso

variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated X.hom]
    [Flat Y.hom] [LocallyOfFinitePresentation Y.hom] [IsSeparated Y.hom]

include z h in
theorem FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofCoordinateIso
    (D : FamilyGroup.Operations.FamilyGroupOperations X) (Pm Pi : Polynomial ℚ)
    (hD : D.ProjectiveGraphBounds (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X) Pm Pi) :
    (D.ofIso e).ProjectiveGraphBounds (⟨n, j, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation Y) Pm Pi :=
  FamilyGroup.Operations.FamilyGroupOperations.ProjectiveGraphBounds.ofBundleIso
    (⟨n, i, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation X)
    (⟨n, j, inferInstance⟩ : Projective.ProjectivePresentations.ProjectivePresentation Y) e
    (PresentedGroupCoordinateTransport.projectiveEmbeddingCoordinateTwistingIso i j e z h) D Pm Pi hD

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
