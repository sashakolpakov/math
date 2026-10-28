import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricSections

/-! # Quasicoherent Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentPullback

noncomputable section

/-! Actual pullback of a quasicoherent module between affine schemes is quasicoherent. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem affine_pullback_quasicoherent {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := by
  let e : (pullback f).obj M ≅ (SectionAdjunction.AffineSectionAdjunction.left X).obj
      ((ModuleCat.extendScalars f.appTop.hom).obj ((SectionAdjunction.AffineSectionAdjunction.sections Y).obj M)) :=
    (pullback f).mapIso (SectionCounit.AffineSectionAdjunction.counitIso Y M).symm ≪≫
      (GeometricSections.AffineGeometricSections.leftComparison f).app _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
    (SectionAdjunction.AffineSectionAdjunction.left_quasicoherent X _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentPullback
