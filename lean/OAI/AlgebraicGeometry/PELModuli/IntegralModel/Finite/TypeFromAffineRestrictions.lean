import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Type From Affine Restrictions -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeFromAffineRestrictions

noncomputable section

/-! Finite global sections on affine restrictions supply actual finite
local generators for a quasicoherent module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem finiteType_of_affine_restriction_sections_finite
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (hfinite : ∀ U : X.affineOpens,
      Module.Finite Γ(U.1.toScheme, ⊤) Γ(M.restrict U.1.ι, ⊤)) :
    M.IsFiniteType := by
  choose G hG using fun U : X.affineOpens => by
    have : IsAffine U.1.toScheme := U.2
    have : Module.Finite Γ(U.1.toScheme, ⊤) Γ(M.restrict U.1.ι, ⊤) := hfinite U
    exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.exists_generatingSections_of_globalSections_module_finite_of_isAffine (M.restrict U.1.ι)
  let q : M.LocalGeneratorsData := {
    I := X.affineOpens
    X := fun U => (U : X.Opens)
    coversTop := by
      rw [Opens.coversTop_iff, IsOpenCover, iSup_affineOpens_eq_top X]
    generators := fun U => SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict M U.1 (G U) }
  have hq : q.IsFiniteType := by
    constructor
    intro U
    let := hG U
    exact SheafCohomology.Projective.Quasicoherent.Scheme.Modules.generatingSectionsOverOfRestrict_isFiniteType M U.1 (G U)
  have hshrink : q.shrink.IsFiniteType := by
    constructor
    intro i
    dsimp [SheafOfModules.LocalGeneratorsData.shrink]
    exact hq.isFiniteType i.2.choose
  exact { exists_localGeneratorsData := ⟨q.shrink, hshrink⟩ }

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.TypeFromAffineRestrictions
