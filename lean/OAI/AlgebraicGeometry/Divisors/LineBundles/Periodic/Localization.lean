import OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Exact
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportLength

/-! # Localization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Localization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: vanishing and finiteness of actual localized periodic homology

An exact localized complex makes every homology representative a
boundary after multiplication by a denominator. If this holds away
from the closed point, the actual homology has finite length.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def localizedEndomorphism (S : Submonoid R) (φ : M →ₗ[R] M) :
    LocalizedModule S M →ₗ[R] LocalizedModule S M :=
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S M) φ

theorem localizedEndomorphism_comp_map (S : Submonoid R) (φ : M →ₗ[R] M) :
    (localizedEndomorphism S φ).comp (LocalizedModule.mkLinearMap S M) =
      (LocalizedModule.mkLinearMap S M).comp φ :=
  IsLocalizedModule.map_comp S (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S M) φ

theorem localizedPeriodicHomology_subsingleton (S : Submonoid R)
    (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0)
    (hex : Function.Exact (localizedEndomorphism S ψ) (localizedEndomorphism S φ)) :
    Subsingleton (LocalizedModule S (Periodic.Exact.BundleCycles.periodicHomology φ ψ hψφ)) := by
  apply LocalizedModule.subsingleton_iff.mpr
  intro q
  obtain ⟨u, rfl⟩ := (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range.mkQ_surjective q
  let f : M →ₗ[R] LocalizedModule S M := LocalizedModule.mkLinearMap S M
  have hfu : localizedEndomorphism S φ (f u.1) = 0 :=
    (LinearMap.congr_fun (localizedEndomorphism_comp_map S φ) u.1).trans
      ((congrArg f u.2).trans f.map_zero)
  obtain ⟨v, hv⟩ := (hex (f u.1)).mp hfu
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S f v
  change (s : R) • v = f m at hs
  have he : f (ψ m) = f ((s : R) • u.1) := by
    calc
      f (ψ m) = localizedEndomorphism S ψ (f m) :=
        (LinearMap.congr_fun (localizedEndomorphism_comp_map S ψ) m).symm
      _ = localizedEndomorphism S ψ ((s : R) • v) := congrArg _ hs.symm
      _ = (s : R) • f u.1 :=
        ((localizedEndomorphism S ψ).map_smul (s : R) v).trans
          (congrArg (fun z => (s : R) • z) hv)
      _ = f ((s : R) • u.1) := (f.map_smul (s : R) u.1).symm
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) he
  change (t : R) • ψ m = (t : R) • ((s : R) • u.1) at ht
  refine ⟨(t : R) * (s : R), S.mul_mem t.2 s.2, ?_⟩
  change (Periodic.Exact.BundleCycles.periodicBoundaryMap φ ψ hψφ).range.mkQ (((t : R) * (s : R)) • u) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨(t : R) • m, Subtype.ext ?_⟩
  exact (ψ.map_smul (t : R) m).trans (ht.trans (mul_smul (t : R) (s : R) u.1).symm)

theorem periodicHomology_length_ne_top_of_local_exact
    [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (φ ψ : M →ₗ[R] M) (hψφ : φ.comp ψ = 0)
    (hs : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Function.Exact (localizedEndomorphism p.asIdeal.primeCompl ψ)
        (localizedEndomorphism p.asIdeal.primeCompl φ)) :
    Module.length R (Periodic.Exact.BundleCycles.periodicHomology φ ψ hψφ) ≠ ⊤ := by
  apply Closed.SupportLength.BundleCycles.moduleLength_ne_top_of_localizations_zero
  intro p hp
  exact localizedPeriodicHomology_subsingleton p.asIdeal.primeCompl φ ψ hψφ (hs p hp)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Periodic.Localization.BundleCycles
