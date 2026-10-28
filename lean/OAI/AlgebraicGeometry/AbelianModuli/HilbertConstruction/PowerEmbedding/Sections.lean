import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.RingSectionBasis

/-! # Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Retain the complete global-section basis of a power embedding.
This distinguishes embeddings by the whole section space from proper
subsystems when the change-of-frame quotient is constructed. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}

structure Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) where
  basis : Module.Basis (Fin (E.dimension + 1)) Γ(S, ⊤)
    ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor X.hom.appTop.hom).obj E.power.sheaf)
  sections_eq : E.sections = Coefficient.RingSectionBasis.coefficientRingBasisFamily X.hom.appTop.hom E.power.sheaf basis

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.HasCompleteSections (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) : Prop := Nonempty E.CompleteSectionData

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
