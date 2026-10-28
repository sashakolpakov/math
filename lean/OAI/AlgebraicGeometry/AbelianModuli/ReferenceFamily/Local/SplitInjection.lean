/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import Mathlib.RingTheory.LocalProperties.Projective

/-! # Split Injection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.SplitInjection

noncomputable section

/-! A linear map between finitely presented modules has a left inverse
when its localization at every maximal ideal has a left inverse. -/

theorem split_injective_of_localization_maximal
    {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N)
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
      ∃ g : LocalizedModule I.primeCompl N →ₗ[Localization.AtPrime I] LocalizedModule I.primeCompl M,
        g.comp (LocalizedModule.map I.primeCompl f) = LinearMap.id) :
    ∃ g : N →ₗ[R] M, g.comp f = LinearMap.id := by
  change LinearMap.id ∈ LinearMap.range (LinearMap.lcomp R M f)
  refine Submodule.mem_of_localization_maximal _ (fun P _ => LocalizedModule.map P.primeCompl) _ _
    fun I hI => ?_
  rw [LocalizedModule.map_id]
  have h : LinearMap.id ∈ LinearMap.range (LinearMap.lcomp (Localization.AtPrime I)
      (LocalizedModule I.primeCompl M) (LocalizedModule.map I.primeCompl f)) := H I hI
  convert! h
  ext k
  constructor
  · intro hk
    obtain ⟨a, ha, c, rfl⟩ := hk
    obtain ⟨g, rfl⟩ := ha
    use IsLocalizedModule.mk' (LocalizedModule.map I.primeCompl) g c
    apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
      (LocalizedModule.map I.primeCompl) c).injective
    dsimp
    conv_rhs => rw [← Submonoid.smul_def]
    conv_lhs => rw [← LinearMap.map_smul_of_tower]
    rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', IsLocalizedModule.mk'_cancel']
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl M)
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl M)
    ext
    simp only [LocalizedModule.map_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, LocalizedModule.mkLinearMap_apply, LinearMap.lcomp_apply,
      LocalizedModule.map_mk]
  · rintro ⟨g, rfl⟩
    obtain ⟨⟨g, s⟩, rfl⟩ :=
      IsLocalizedModule.mk'_surjective I.primeCompl (LocalizedModule.map I.primeCompl) g
    simp only [Function.uncurry_apply_pair]
    refine ⟨g.comp f, ⟨g, rfl⟩, s, ?_⟩
    apply ((Module.End.isUnit_iff _).mp <| IsLocalizedModule.map_units
      (LocalizedModule.map I.primeCompl) s).injective
    simp only [Module.algebraMap_end_apply, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel',
      ← LinearMap.map_smul_of_tower]
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.ext I.primeCompl (LocalizedModule.mkLinearMap I.primeCompl M)
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap I.primeCompl M)
    ext
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, LinearMap.lcomp_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Local.SplitInjection
