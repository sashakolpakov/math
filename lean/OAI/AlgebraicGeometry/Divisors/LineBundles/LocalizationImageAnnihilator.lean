import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationLength

/-! # Localization Image Annihilator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationImageAnnihilator.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual annihilator of a branch image

An element kills the localization image precisely when it kills the
whole localization. For a quotient R/I, the resulting annihilator is
the contraction of I after localization.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem localizationImage_annihilator_eq (S : Submonoid R) :
    Module.annihilator R (LocalizationImage.BundleCycles.localizationImage S M) = Module.annihilator R (LocalizedModule S M) := by
  ext r
  rw [Module.mem_annihilator, Module.mem_annihilator]
  constructor
  · intro hr m
    let f := (LocalizationImage.BundleCycles.localizationImage S M).subtype
    obtain ⟨⟨u, s⟩, hs⟩ := IsLocalizedModule.surj S f m
    apply IsLocalizedModule.smul_injective f s
    change (s : R) • (r • m) = (s : R) • 0
    calc
      (s : R) • (r • m) = r • ((s : R) • m) := smul_comm _ _ _
      _ = r • f u := congrArg (fun z => r • z) hs
      _ = f (r • u) := (f.map_smul r u).symm
      _ = 0 := (congrArg f (hr u)).trans f.map_zero
      _ = (s : R) • 0 := (smul_zero _).symm
  · intro hr m
    exact Subtype.ext (hr m.1)

theorem localizationImage_quotient_annihilator (S : Submonoid R) (I : Ideal R) :
    Module.annihilator R (LocalizationImage.BundleCycles.localizationImage S (R ⧸ I)) =
      (I.map (algebraMap R (Localization S))).under R := by
  rw [localizationImage_annihilator_eq,
    ← Module.comap_annihilator (R := Localization S) (R₀ := R),
    (LocalizedEquationLength.BundleCycles.localizedIdealQuotientEquiv S I).annihilator_eq, Ideal.annihilator_quotient]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationImageAnnihilator.BundleCycles
