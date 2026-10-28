import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModuleSupportAnnihilation
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Maximal

/-! # Point Module Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointModuleLocalization

noncomputable section

/-! A finite module supported at one closed point is unchanged by localization at that point. Scalars outside the maximal ideal acquire explicit inverses on the module. -/
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem singlePointSupported_scalar_inverse
    (m : Ideal R) [m.IsMaximal]
    (hSupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (m : Set R))
    (s : R) (hs : s ∉ m) : ∃ t : R, ∀ x : M, t • (s • x) = x := by
  have hrad : m ≤ (Module.annihilator R M).radical := by
    rwa [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hSupport
  have hsup : Module.annihilator R M ⊔ Ideal.span ({s} : Set R) = ⊤ := by
    by_contra hn
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hn
    have hm : m ≤ q := hrad.trans
      ((Ideal.radical_mono (le_sup_left.trans hle)).trans_eq hq.isPrime.radical)
    have heq : m = q := (inferInstance : m.IsMaximal).eq_of_le hq.ne_top hm
    have hsq : s ∈ q := hle
      ((show Ideal.span ({s} : Set R) ≤ Module.annihilator R M ⊔ Ideal.span ({s} : Set R)
        from le_sup_right) (Ideal.subset_span (Set.mem_singleton s)))
    exact hs (by simpa only [heq] using hsq)
  have h1 : (1 : R) ∈ Module.annihilator R M ⊔ Ideal.span ({s} : Set R) := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨t, fun x => ?_⟩
  have hax : a • x = 0 := Module.mem_annihilator.mp ha x
  have h := congrArg (fun r : R => r • x) hab
  simpa only [add_smul, hax, zero_add, mul_smul, one_smul] using h

theorem singlePointSupported_scalar_bijective
    (m : Ideal R) [m.IsMaximal]
    (hSupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (m : Set R))
    (s : R) (hs : s ∉ m) : Function.Bijective (fun x : M => s • x) := by
  obtain ⟨t, ht⟩ := singlePointSupported_scalar_inverse m hSupport s hs
  constructor
  · intro x y h
    exact (ht x).symm.trans ((congrArg (fun z : M => t • z) h).trans (ht y))
  · intro y
    exact ⟨t • y, (smul_comm s t y).trans (ht y)⟩

theorem singlePointSupported_isLocalizedIdentity
    (m : Ideal R) [m.IsMaximal]
    (hSupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (m : Set R)) :
    IsLocalizedModule m.primeCompl (LinearMap.id : M →ₗ[R] M) where
  map_units s := (Module.End.isUnit_iff _).mpr
    (singlePointSupported_scalar_bijective m hSupport s s.property)
  surj y := ⟨(y, 1), by simp⟩
  exists_of_eq h := ⟨1, by simpa using h⟩

def singlePointSupportedLocalizationEquiv
    (m : Ideal R) [m.IsMaximal]
    (hSupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (m : Set R)) :
    M ≃ₗ[R] LocalizedModule m.primeCompl M := by
  letI := singlePointSupported_isLocalizedIdentity m hSupport
  exact (IsLocalizedModule.iso m.primeCompl (LinearMap.id : M →ₗ[R] M)).symm

theorem singlePointSupportedLocalizationEquiv_toLinearMap
    (m : Ideal R) [m.IsMaximal]
    (hSupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (m : Set R)) :
    (singlePointSupportedLocalizationEquiv m hSupport).toLinearMap = LocalizedModule.mkLinearMap m.primeCompl M := by
  let := singlePointSupported_isLocalizedIdentity m hSupport
  change (IsLocalizedModule.iso m.primeCompl (LinearMap.id : M →ₗ[R] M)).symm.toLinearMap = _
  simpa only [LinearMap.comp_id] using
    (IsLocalizedModule.iso_symm_comp m.primeCompl (LinearMap.id : M →ₗ[R] M))

theorem singlePointSupported_subsingleton_of_localization
    (m : Ideal R) [m.IsMaximal]
    (hSupport : Module.support R M ⊆ PrimeSpectrum.zeroLocus (m : Set R))
    (hzero : Subsingleton (LocalizedModule m.primeCompl M)) : Subsingleton M :=
  ⟨fun x y => (singlePointSupportedLocalizationEquiv m hSupport).injective
    (hzero.elim ((singlePointSupportedLocalizationEquiv m hSupport) x)
      ((singlePointSupportedLocalizationEquiv m hSupport) y))⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.PointModuleLocalization
