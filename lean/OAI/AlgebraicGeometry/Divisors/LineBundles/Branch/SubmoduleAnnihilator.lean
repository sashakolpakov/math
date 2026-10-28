import OAI.AlgebraicGeometry.Divisors.LineBundles.MinimalBranchRadical

/-! # Submodule Annihilator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.SubmoduleAnnihilator.BundleCycles

noncomputable section

/-!
# LineBundleCycles: nonzero submodules of the actual branch image have radical P

The original annihilator still kills the submodule. Conversely, an
element outside P acts injectively on the localization image and
cannot annihilate a nonzero submodule.
-/

variable {R : Type*} [CommRing R]

theorem localizationImage_submodule_annihilator_radical
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes)
    (N : Submodule R (LocalizationImage.BundleCycles.localizationImage P.primeCompl (R ⧸ I))) [Nontrivial N] :
    (Module.annihilator R N).radical = P := by
  have hle : Module.annihilator R (LocalizationImage.BundleCycles.localizationImage P.primeCompl (R ⧸ I)) ≤
      Module.annihilator R N :=
    N.subtype.annihilator_le_of_injective N.subtype_injective
  have hAnn : Module.annihilator R N ≤ P := by
    intro r hr
    by_contra hrP
    obtain ⟨n, hn⟩ := exists_ne (0 : N)
    apply hn
    apply N.subtype_injective
    apply LocalizationImage.BundleCycles.localizationImage_equation_injective P.primeCompl ⟨r, hrP⟩
    have hz : r • n.1 = 0 := congrArg (fun z : N => z.1) (Module.mem_annihilator.mp hr n)
    exact hz.trans (map_zero (MultiplicationSequence.BundleCycles.equationEndomorphism r (LocalizationImage.BundleCycles.localizationImage P.primeCompl (R ⧸ I)))).symm
  apply le_antisymm ((inferInstance : P.IsPrime).radical_le_iff.mpr hAnn)
  exact (MinimalBranchRadical.BundleCycles.minimalPrime_branch_annihilator_radical I P hP).symm.le.trans (Ideal.radical_mono hle)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Branch.SubmoduleAnnihilator.BundleCycles
