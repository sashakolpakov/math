import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Compactification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoordinateProjectivePresentation

/-! # Compactification Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine

noncomputable section

/-! Affine compactifications carry HilbertConstruction's actual projective and quasi-projective presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}

def Compactification.AffineCompactification.Data.projectivePresentation (D : Compactification.AffineCompactification.Data f) : Projective.ProjectivePresentations.ProjectivePresentation (Over.mk D.base) := by
  let : Fintype D.coordinates := Fintype.ofFinite D.coordinates
  exact Finite.CoordinateProjectivePresentation.finiteCoordinateProjectivePresentation D.base D.embedding D.embedding_base

def Compactification.AffineCompactification.Data.quasiProjectivePresentation (D : Compactification.AffineCompactification.Data f) [LocallyOfFiniteType f] [QuasiCompact f] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Over.mk f) where
  locallyFiniteType := inferInstanceAs (LocallyOfFiniteType f)
  quasiCompact := inferInstanceAs (QuasiCompact f)
  compactification := Over.mk D.base
  projective := D.projectivePresentation
  embedding := Over.homMk D.chart D.chart_base
  openImmersion := D.openImmersion

def CompactificationPresentation.AffineCompactification.affineFinitePresentationQuasiProjective [IsAffine X]
    (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Over.mk f) :=
  (Compactification.AffineCompactification.ofAffine f).quasiProjectivePresentation

def CompactificationPresentation.AffineCompactification.affineFiniteTypeQuasiProjective [IsAffine X] [IsNoetherianRing R]
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (Over.mk f) :=
  (Compactification.AffineCompactification.ofFiniteType f).quasiProjectivePresentation

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine
