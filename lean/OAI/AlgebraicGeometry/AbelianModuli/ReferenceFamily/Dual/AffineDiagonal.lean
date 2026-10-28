import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReductionOpens
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine Diagonal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDiagonal

noncomputable section

/-! The actual dual-number family over a separated complex scheme
has affine diagonal, so the constructed affine-frame intersections apply. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem dualFamily_affineDiagonal (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsSeparated X.hom] :
    IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left)) := by
  let : IsSeparated (LieRanks.dualNumberTest ℂ).hom := by
    change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))))
    infer_instance
  let : IsSeparated (LieRanks.dualNumberTest ℂ ⊗ X).hom := by
    change IsSeparated (pullback.fst (LieRanks.dualNumberTest ℂ).hom X.hom ≫ (LieRanks.dualNumberTest ℂ).hom)
    infer_instance
  let : IsSeparated (terminal.from Foundations.Scheme.ProjectiveSpace.complexBase) := by infer_instance
  have h : IsSeparated ((LieRanks.dualNumberTest ℂ ⊗ X).hom ≫ terminal.from Foundations.Scheme.ProjectiveSpace.complexBase) := inferInstance
  have he : (LieRanks.dualNumberTest ℂ ⊗ X).hom ≫ terminal.from Foundations.Scheme.ProjectiveSpace.complexBase =
      terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left := Subsingleton.elim _ _
  let : IsSeparated (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left) := he ▸ h
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.AffineDiagonal
