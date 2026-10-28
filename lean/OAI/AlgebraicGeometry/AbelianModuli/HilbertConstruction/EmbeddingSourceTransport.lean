import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoefficientSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.SourceIsomorphism

/-! # Embedding Source Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Source isomorphisms retain complete section bases of the actual
transported power embedding, together with degree and ambient dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X Y : Over S} {L : Line.Bundles.LineBundle Y.left} {M : Line.Bundles.LineBundle X.left}
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L Y.hom) (D : E.CompleteSectionData)
variable (e : X ≅ Y) (eL : (L.pullback e.hom.left).sheaf ≅ M.sheaf)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData.ofSourceIso : (E.ofSourceIso e eL).CompleteSectionData where
  basis := D.basis.map (IsoCoefficientSectionBasis.sourceIsoCoefficientSectionEquiv e E.power.sheaf)
  sections_eq := by
    change (fun i => Ample.LineBundles.pullbackSection e.hom.left (E.sections i)) = _
    rw [D.sections_eq]
    funext i
    exact (IsoCoefficientSectionBasis.coefficientRingBasisFamily_sourceIso e E.power.sheaf D.basis i).symm

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.HasCompleteSections.ofSourceIso (hE : E.HasCompleteSections) : (E.ofSourceIso e eL).HasCompleteSections := by
  obtain ⟨D⟩ := hE
  exact ⟨D.ofSourceIso E e eL⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
