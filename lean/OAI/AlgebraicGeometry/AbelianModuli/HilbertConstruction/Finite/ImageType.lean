import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections

/-! # Image Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageType

noncomputable section

/-! Finite direct images of finite-type quasicoherent sheaves are finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem finite_directImage_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pushforward f).obj M).IsFiniteType := by
  have : ((pushforward f).obj M).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f M
  exact TypeFromAffineSections.module_finiteType_of_affine_sections_finite _ (ImageSections.finite_directImage_affine_sections_finite f M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ImageType
