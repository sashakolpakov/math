import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModuleVanishingOpen
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ModuleAnnihilation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Module Vanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ModuleVanishing

noncomputable section

/-! On an affine scheme the vanishing open of a finite quasicoherent
module is the complement of the zero locus of its actual annihilator. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem module_sections_subsingleton_of_isZero {X : Scheme.{u}}
    (M : X.Modules) (hM : IsZero M) (U : X.Opens) : Subsingleton Γ(M, U) := by
  have hz (x : Γ(M, U)) : x = 0 := by
    have h := congrArg (fun a : M ⟶ M => a.app U x) (hM.eq_of_src (𝟙 M) 0)
    exact h
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem affineModule_isZero_iff_globalSections_subsingleton
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    IsZero M ↔ Subsingleton Γ(M, ⊤) := by
  refine ⟨fun h => module_sections_subsingleton_of_isZero M h ⊤, fun h => ?_⟩
  let := h
  have ha : IsIso ((0 : M ⟶ M).val.app (op ⊤)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (fun _ : Γ(M, ⊤) => (0 : Γ(M, ⊤)))
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  have : IsIso (0 : M ⟶ M) := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top 0 ha
  exact IsZero.of_mono_zero M M

theorem module_restrict_isZero_iff_sections_subsingleton
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsZero (M.restrict U.ι) ↔ Subsingleton Γ(M, U) := by
  let : IsAffine U.toScheme := hU
  rw [affineModule_isZero_iff_globalSections_subsingleton]
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
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M U
  let : Module Γ(X, U.1) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r))
  let g : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen r) :=
    { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r)).op
      map_add' := (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.map_add
      map_smul' := fun a x => M.map_smul (homOfLE (X.basicOpen_le r)) a x }
  have : IsLocalizedModule.Away r g :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen M U r
  exact IntegralModel.Finite.ModuleAnnihilation.finite_away_subsingleton_iff_pow_annihilator r g

theorem affineModule_basicOpen_isZero_iff_pow_annihilator
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (r : Γ(X, ⊤)) :
    IsZero (M.restrict (X.basicOpen r).ι) ↔
      ∃ n : ℕ, r ^ n ∈ Module.annihilator Γ(X, ⊤) Γ(M, ⊤) :=
  affineOpenModule_basicOpen_isZero_iff_pow_annihilator M ⟨⊤, isAffineOpen_top X⟩ r

theorem affineModule_mem_vanishingOpen_iff
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (x : X) :
    x ∈ ModuleVanishingOpen.moduleVanishingOpen M ↔
      ¬ Module.annihilator Γ(X, ⊤) Γ(M, ⊤) ≤ (X.isoSpec.hom x).asIdeal := by
  have hbasic (r : Γ(X, ⊤)) :
      x ∈ X.basicOpen r ↔ r ∉ (X.isoSpec.hom x).asIdeal := by
    rw [← Scheme.map_PrimeSpectrum_basicOpen_of_affine X r]
    rfl
  constructor
  · intro hx hann
    obtain ⟨U, hxU, hU⟩ := (ModuleVanishingOpen.mem_moduleVanishingOpen M x).mp hx
    obtain ⟨r, hrU, hxr⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hxU⟩ (by trivial)
    have hz := ModuleVanishingOpen.module_restrict_isZero_of_le M hrU hU
    obtain ⟨n, hn⟩ := (affineModule_basicOpen_isZero_iff_pow_annihilator M r).mp hz
    exact (hbasic r).mp hxr ((X.isoSpec.hom x).isPrime.mem_of_pow_mem n (hann hn))
  · intro h
    obtain ⟨r, hr, hxr⟩ := SetLike.not_le_iff_exists.mp h
    exact (ModuleVanishingOpen.mem_moduleVanishingOpen M x).mpr ⟨X.basicOpen r, (hbasic r).mpr hxr,
      (affineModule_basicOpen_isZero_iff_pow_annihilator M r).mpr ⟨1, by simpa using hr⟩⟩

theorem affineModule_vanishingOpen_compl_eq_support
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ((ModuleVanishingOpen.moduleVanishingOpen M : X.Opens) : Set X)ᶜ =
      X.isoSpec.hom ⁻¹' Module.support Γ(X, ⊤) Γ(M, ⊤) := by
  have : Module.Finite Γ(X, ⊤) Γ(M, ⊤) :=
    SheafCohomology.Projective.Quasicoherent.Scheme.Modules.globalSections_module_finite_of_isFiniteType_of_isAffine M
  ext x
  change (¬ x ∈ ModuleVanishingOpen.moduleVanishingOpen M) ↔
    X.isoSpec.hom x ∈ Module.support Γ(X, ⊤) Γ(M, ⊤)
  rw [affineModule_mem_vanishingOpen_iff, not_not]
  exact (Module.mem_support_iff_of_finite (R := Γ(X, ⊤))
    (M := Γ(M, ⊤)) (p := X.isoSpec.hom x)).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ModuleVanishing
