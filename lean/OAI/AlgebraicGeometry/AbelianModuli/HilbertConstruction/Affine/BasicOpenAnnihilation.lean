import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleZeroCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LocalizationAnnihilation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentFiniteTypeSections

/-! # Basic Open Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasicOpenAnnihilation

noncomputable section

/- Adapted from the IntegralModel affine module vanishing argument with HilbertConstruction's checked quasicoherent localization theorems. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem module_restrict_isZero_iff_sections_subsingleton
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsZero (M.restrict U.ι) ↔ Subsingleton Γ(M, U) := by
  let : IsAffine U.toScheme := hU
  rw [ModuleZeroCriterion.affineModule_isZero_iff_globalSections_subsingleton]
  let e := M.restrictAppIso U.ι ⊤ ≪≫
    M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
  exact ⟨fun h => by
    let := h
    exact (ConcreteCategory.bijective_of_isIso e.inv).injective.subsingleton,
    fun h => by
      let := h
      exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton⟩

theorem affineOpenModule_basicOpen_isZero_iff_pow_annihilator
    {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (U : X.affineOpens) (r : Γ(X, U.1)) :
    IsZero (M.restrict (X.basicOpen r).ι) ↔
      ∃ n : ℕ, r ^ n ∈ Module.annihilator Γ(X, U.1) Γ(M, U.1) := by
  rw [module_restrict_isZero_iff_sections_subsingleton M _ (U.2.basicOpen r)]
  let : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
    QuasicoherentFiniteTypeSections.affineOpen_quasicoherent_finiteType_sections_finite M U
  let : Module Γ(X, U.1) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r))
  let g : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen r) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r)).op
      map_add' := (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.map_add
      map_smul' := fun a x => M.map_smul (homOfLE (X.basicOpen_le r)) a x }
  have : IsLocalizedModule.Away r g :=
    AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize M U r
  exact HilbertConstruction.Finite.LocalizationAnnihilation.finite_away_subsingleton_iff_pow_annihilator r g

theorem affineModule_basicOpen_isZero_iff_pow_annihilator
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (r : Γ(X, ⊤)) :
    IsZero (M.restrict (X.basicOpen r).ι) ↔
      ∃ n : ℕ, r ^ n ∈ Module.annihilator Γ(X, ⊤) Γ(M, ⊤) :=
  affineOpenModule_basicOpen_isZero_iff_pow_annihilator M ⟨⊤, isAffineOpen_top X⟩ r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasicOpenAnnihilation
