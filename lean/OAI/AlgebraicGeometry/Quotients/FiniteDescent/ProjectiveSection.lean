import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveBaseRingModel
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FiberSection

/-! # Projective Section -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveSection.Construction.ProjectiveSectionSupport

noncomputable section

/-! In a flat projective family over a Noetherian affine base, the nonzero
fiber-section locus of a line bundle is closed. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom]

include P

theorem isClosed (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left) :
    IsClosed (FiberSection.Construction.FiberSectionSupport.locus X.hom L.sheaf) := by
  obtain ⟨D, φ, _, _, hfin, hproj, hφ⟩ :=
    ProjectiveBaseRingModel.Construction.ProjectiveCechComplex.exists_actual_finite_projective X P L
  have := hfin 0
  have := hfin 1
  have := hproj 0
  have := hproj 1
  have : L.sheaf.IsQuasicoherent := LineBundleFree.Construction.LineBundleCoherence.quasicoherent L
  exact FiberSection.Construction.FiberSectionSupport.isClosed_of_model X.hom L.sheaf
    (ProjectiveCechAt.Construction.ProjectiveCechComplex.cover X P) (ProjectiveCechAt.Construction.ProjectiveCechComplex.covers X P) φ
    (fun q i => ProjectiveCechFlat.Construction.ProjectiveCechComplex.intersection_affine X P q i.1) hφ

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProjectiveSection.Construction.ProjectiveSectionSupport
