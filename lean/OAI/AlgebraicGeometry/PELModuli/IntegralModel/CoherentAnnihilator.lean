import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ModuleVanishing
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AnnihilatorLocalization
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Coherent Annihilator -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentAnnihilator

noncomputable section

/-! The actual annihilator ideal sheaf of a finite quasicoherent module,
with its closed support identified by the maximal vanishing open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def coherentAnnihilator {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : X.IdealSheafData where
  ideal U := Module.annihilator Γ(X, U.1) Γ(M, U.1)
  map_ideal_basicOpen U r := by
    let : Module.Finite Γ(X, U.1) Γ(M, U.1) :=
      SheafCohomology.Projective.Quasicoherent.Scheme.Modules.sections_module_finite_of_isFiniteType_of_isAffineOpen M U
    let : Module Γ(X, U.1) Γ(M, X.basicOpen r) :=
      Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen r))
    let : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
      .of_algebraMap_smul fun _ _ => rfl
    let : IsLocalization.Away r Γ(X, X.basicOpen r) := U.2.isLocalization_basicOpen r
    let g : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(M, X.basicOpen r) :=
      { toFun := M.presheaf.map (homOfLE (X.basicOpen_le r)).op
        map_add' := (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.map_add
        map_smul' := fun a x => M.map_smul (homOfLE (X.basicOpen_le r)) a x }
    have : IsLocalizedModule.Away r g :=
      SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isLocalizedModuleAway_basicOpen_of_isQuasicoherent_of_isAffineOpen M U r
    change (Module.annihilator Γ(X, U.1) Γ(M, U.1)).map
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      Module.annihilator Γ(X, X.basicOpen r) Γ(M, X.basicOpen r)
    exact AnnihilatorLocalization.annihilator_map_eq_of_isLocalizedModule (Submonoid.powers r)
      Γ(X, X.basicOpen r) g

theorem coherentAnnihilator_mem_support_iff {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (x : X) :
    x ∈ (coherentAnnihilator M).support ↔ x ∉ ModuleVanishingOpen.moduleVanishingOpen M := by
  constructor
  · intro hx hv
    obtain ⟨V, hxV, hV⟩ := (ModuleVanishingOpen.mem_moduleVanishingOpen M x).mp hv
    let U : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
    have hxU : x ∈ U.1 := X.affineCover.covers x
    obtain ⟨r, hrV, hxr⟩ := U.2.exists_basicOpen_le ⟨x, hxV⟩ hxU
    obtain ⟨n, hn⟩ := (Affine.ModuleVanishing.affineOpenModule_basicOpen_isZero_iff_pow_annihilator M U r).mp
      (ModuleVanishingOpen.module_restrict_isZero_of_le M hrV hV)
    have hz : x ∈ X.zeroLocus (U := U.1)
        (Module.annihilator Γ(X, U.1) Γ(M, U.1)).radical := by
      rw [X.zeroLocus_radical]
      exact (coherentAnnihilator M).mem_support_iff_of_mem hxU |>.mp hx
    exact (X.mem_zeroLocus_iff _ x).mp hz r ⟨n, hn⟩ hxr
  · intro hx
    rw [(coherentAnnihilator M).mem_support_iff]
    intro U
    rw [X.mem_zeroLocus_iff]
    intro r hr hxr
    change r ∈ Module.annihilator Γ(X, U.1) Γ(M, U.1) at hr
    apply hx
    exact (ModuleVanishingOpen.mem_moduleVanishingOpen M x).mpr ⟨X.basicOpen r, hxr,
      (Affine.ModuleVanishing.affineOpenModule_basicOpen_isZero_iff_pow_annihilator M U r).mpr
        ⟨1, by simpa using hr⟩⟩

theorem coherentAnnihilator_support_eq {X : Scheme.{u}} (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ((coherentAnnihilator M).support : Set X) =
      ((ModuleVanishingOpen.moduleVanishingOpen M : X.Opens) : Set X)ᶜ := by
  ext x
  exact coherentAnnihilator_mem_support_iff M x

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentAnnihilator
