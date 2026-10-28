import OAI.RepresentationTheory.Theta.Geometric.HyperplanePullbackAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.ProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

/-! # Projective Presentation -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.ProjectivePresentation

noncomputable section

/-! A finite cover of an actually projectively embedded complex scheme
has a constructed projective embedding of the very same source scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.ClosedProjective

def finiteProjectivePresentation {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom) (f : X ⟶ Y) [IsFinite f.left] :
    AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom := by
  let : IsProper Y.hom := P.isProper
  let : IsProper X.hom := f.w ▸ inferInstanceAs (IsProper (f.left ≫ Y.hom))
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let i := f.left ≫ P.embedding
  have : IsAffineHom i := inferInstanceAs (IsAffineHom (f.left ≫ P.embedding))
  let h := HyperplanePullbackAmpleness.hyperplanePullback_isAmple i
  exact AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
    (h.projectivePresentation X.hom)

def finiteEtaleSmoothProjectivePresentation {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom) [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation where
  carrier := X.left
  structureMap := X.hom
  projective := finiteProjectivePresentation P f
  smooth := f.w ▸ inferInstanceAs (Smooth (f.left ≫ Y.hom))

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.ProjectivePresentation
