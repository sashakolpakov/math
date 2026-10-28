import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.LineBundleSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectiveChowModification

/-! # Line Bundle Section Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow

noncomputable section

/-! Every actual line bundle on the constructed Chow modification has a finite module of global sections over the Noetherian affine coefficient base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

theorem Modification.ChowModification.Model.lineBundleSections_finite (D : Modification.ChowModification.Model f) (L : Line.Bundles.LineBundle D.scheme) :
    Module.Finite R ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (D.projection ≫ f)).obj L.sheaf) :=
  D.projectivePresentation.lineBundleSections_finite L

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chow
