import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Localization Spectrum Is -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationSpectrumIs.LocalizationSpectrum

noncomputable section

/-!
# Principal-localization ring maps as actual open immersions

The localization property of a specified ring map identifies the image
of its actual spectrum map with the corresponding principal open.
-/

open _root_.AlgebraicGeometry

universe u

variable (R S : Type u) [CommRing R] [CommRing S] (f : R →+* S) (s : R)
  (hf : (Submonoid.powers s).IsLocalizationMap f)

include hf in
theorem isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := by
  let : Algebra R S := f.toAlgebra
  have : IsLocalization.Away s S := ⟨hf⟩
  exact IsOpenImmersion.of_isLocalization s

include hf in
theorem range : Set.range (PrimeSpectrum.comap f) = PrimeSpectrum.basicOpen s := by
  let : Algebra R S := f.toAlgebra
  have : IsLocalization.Away s S := ⟨hf⟩
  exact PrimeSpectrum.localization_away_comap_range S s

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationSpectrumIs.LocalizationSpectrum
