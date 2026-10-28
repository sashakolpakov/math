import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.IsoImage
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Module Presentations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModulePresentations

noncomputable section

/-! Quasicoherent modules on affine schemes have actual global presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

def quasicoherentSpecPresentation {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] : M.Presentation := by
  have hIso : IsIso M.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ M).mp inferInstance
  let P : (tilde (moduleSpecΓFunctor.obj M)).Presentation :=
    presentationTilde (moduleSpecΓFunctor.obj M) Set.univ (by simp) _ (Submodule.span_eq _)
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ M.fromTildeΓ hIso P

def quasicoherentAffinePresentation {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] : M.Presentation := by
  let N := M.restrict X.isoSpec.inv
  let P : ((M.restrict X.isoSpec.inv).restrict X.isoSpec.hom).Presentation :=
    presentationRestrict X.isoSpec.hom (quasicoherentSpecPresentation N)
  let e := (LineBundle.IsoImage.restrictFunctorInverseIso X.isoSpec).app M
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ e.hom e.isIso_hom P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModulePresentations
