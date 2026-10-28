import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.TwistingSectionsFinite
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow.AmpleLine

/-! # Ample Power Sections Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The ample powers on the constructed Chow modification have finite modules of actual global sections over a Noetherian coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem Projective.ProjectivePresentations.ProjectivePresentation.amplePowerSections_finite
    {X : Over (Spec (.of R))} (P : Projective.ProjectivePresentations.ProjectivePresentation X) (d : ℕ) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj
      (P.ampleLineBundle.tensorPower d).sheaf) :=
  RelativeProjective.TwistingSectionsFinite.relativeEmbedding_twistingPowerSections_finite_noetherian P.embedding d

theorem Chow.Modification.ChowModification.Model.amplePowerSections_finite
    {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} (D : Chow.Modification.ChowModification.Model f) (d : ℕ) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (D.projection ≫ f)).obj
      (D.ampleLineBundle.tensorPower d).sheaf) :=
  D.projectivePresentation.amplePowerSections_finite d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
