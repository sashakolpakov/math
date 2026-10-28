import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.Sections

/-! # Presentation Section Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Complete section data for a specified projective presentation. It
survives changing the sheaf representing its line bundle, so a complete
power embedding also has a complete canonical graph-power presentation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
section
variable {S : Scheme.{u}} {X : Over S} {P : Projective.ProjectivePresentations.ProjectivePresentation X}
variable {L M : Line.Bundles.LineBundle X.left}

structure Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData (D : P.SectionData L) where
  basis : Module.Basis (Fin (P.dimension + 1)) Γ(S, ⊤)
    ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor X.hom.appTop.hom).obj L.sheaf)
  sections_eq : D.sections = Coefficient.RingSectionBasis.coefficientRingBasisFamily X.hom.appTop.hom L.sheaf basis

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData.ofBundleIso {D : P.SectionData L} (C : D.CompleteData)
    (e : L.sheaf ≅ M.sheaf) : (D.ofBundleIso e).CompleteData where
  basis := C.basis.map (Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv X.hom.appTop.hom e)
  sections_eq := by
    funext i
    change D.sections i ≫ e.hom = _
    exact (congrArg (fun s => s ≫ e.hom) (congrFun C.sections_eq i)).trans
      (Coefficient.SectionBundleTransport.coefficientRingBasisFamily_bundleIso X.hom.appTop.hom e C.basis i).symm
end

variable {S : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (D : E.CompleteSectionData)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData.presentationCompleteData : E.sectionData.CompleteData where
  basis := D.basis
  sections_eq := D.sections_eq

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData.canonicalPowerCompleteData : E.canonicalPowerSectionData.CompleteData :=
  (D.presentationCompleteData E).ofBundleIso
    (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
