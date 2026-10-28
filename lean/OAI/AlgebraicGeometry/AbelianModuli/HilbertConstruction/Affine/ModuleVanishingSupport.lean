import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasicOpenAnnihilation

/-! # Module Vanishing Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleVanishingSupport

noncomputable section

/- Adapted from the IntegralModel affine module vanishing argument with HilbertConstruction's checked quasicoherent localization theorems. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem affineModule_mem_vanishingOpen_iff
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (x : X) :
    x ∈ HilbertConstruction.Module.VanishingOpen.moduleVanishingOpen M ↔
      ¬ Module.annihilator Γ(X, ⊤) Γ(M, ⊤) ≤ (X.isoSpec.hom x).asIdeal := by
  have hbasic (r : Γ(X, ⊤)) :
      x ∈ X.basicOpen r ↔ r ∉ (X.isoSpec.hom x).asIdeal := by
    rw [← Scheme.map_PrimeSpectrum_basicOpen_of_affine X r]
    rfl
  constructor
  · intro hx hann
    obtain ⟨U, hxU, hU⟩ := (HilbertConstruction.Module.VanishingOpen.mem_moduleVanishingOpen M x).mp hx
    obtain ⟨r, hrU, hxr⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hxU⟩ (by trivial)
    have hz := HilbertConstruction.Module.VanishingOpen.module_restrict_isZero_of_le M hrU hU
    obtain ⟨n, hn⟩ := (BasicOpenAnnihilation.affineModule_basicOpen_isZero_iff_pow_annihilator M r).mp hz
    exact (hbasic r).mp hxr ((X.isoSpec.hom x).isPrime.mem_of_pow_mem n (hann hn))
  · intro h
    obtain ⟨r, hr, hxr⟩ := SetLike.not_le_iff_exists.mp h
    exact (HilbertConstruction.Module.VanishingOpen.mem_moduleVanishingOpen M x).mpr ⟨X.basicOpen r, (hbasic r).mpr hxr,
      (BasicOpenAnnihilation.affineModule_basicOpen_isZero_iff_pow_annihilator M r).mpr ⟨1, by simpa using hr⟩⟩

theorem affineModule_vanishingOpen_compl_eq_support
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    ((HilbertConstruction.Module.VanishingOpen.moduleVanishingOpen M : X.Opens) : Set X)ᶜ =
      X.isoSpec.hom ⁻¹' Module.support Γ(X, ⊤) Γ(M, ⊤) := by
  have : Module.Finite Γ(X, ⊤) Γ(M, ⊤) :=
    QuasicoherentFiniteTypeSections.affine_quasicoherent_finiteType_sections_finite M
  ext x
  change (¬ x ∈ HilbertConstruction.Module.VanishingOpen.moduleVanishingOpen M) ↔
    X.isoSpec.hom x ∈ Module.support Γ(X, ⊤) Γ(M, ⊤)
  rw [affineModule_mem_vanishingOpen_iff, not_not]
  exact (Module.mem_support_iff_of_finite (R := Γ(X, ⊤))
    (M := Γ(M, ⊤)) (p := X.isoSpec.hom x)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ModuleVanishingSupport
