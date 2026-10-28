import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionAdjunction

/-! # Section Counit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionCounit.AffineSectionAdjunction

noncomputable section

/-! The actual affine global-sections adjunction recovers each quasicoherent module. -/
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
universe u

theorem counit_isIso (X : Scheme.{u}) [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((SectionAdjunction.AffineSectionAdjunction.adjunction X).counit.app M) := by
  have : ((SectionAdjunction.AffineSectionAdjunction.left X).obj ((SectionAdjunction.AffineSectionAdjunction.sections X).obj M)).IsQuasicoherent := SectionAdjunction.AffineSectionAdjunction.left_quasicoherent X _
  let c : (SectionAdjunction.AffineSectionAdjunction.left X).obj ((SectionAdjunction.AffineSectionAdjunction.sections X).obj M) ⟶ M := (SectionAdjunction.AffineSectionAdjunction.adjunction X).counit.app M
  have hc : IsIso ((SectionAdjunction.AffineSectionAdjunction.sections X).map c) :=
    inferInstanceAs (IsIso ((SectionAdjunction.AffineSectionAdjunction.sections X).map ((SectionAdjunction.AffineSectionAdjunction.adjunction X).counit.app M)))
  exact ModuleGlobalSectionsIsomorphism.affineModule_isIso_of_globalSections_isIso c hc

def counitIso (X : Scheme.{u}) [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    (SectionAdjunction.AffineSectionAdjunction.left X).obj ((SectionAdjunction.AffineSectionAdjunction.sections X).obj M) ≅ M := by
  have := counit_isIso X M
  exact asIso ((SectionAdjunction.AffineSectionAdjunction.adjunction X).counit.app M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionCounit.AffineSectionAdjunction
