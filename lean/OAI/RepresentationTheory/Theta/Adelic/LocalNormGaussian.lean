import OAI.RepresentationTheory.Theta.Adelic.NonarchimedeanNormGaussian
import OAI.RepresentationTheory.Theta.Adelic.RealNormGaussian
import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport
import OAI.RepresentationTheory.Weil.Local.Analytic

/-! # Local Norm Gaussian -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalNormGaussian

noncomputable section

/-! The actual quadratic norm-character identity over every characteristic
zero local field, with its given norm and Haar normalization. -/

open OAI.RepresentationTheory.Weil.Local.Analytic.Construction OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.QuadraticNormTransport

theorem norm_character_gaussian_identity
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ)
    (hc : Continuous (fun x : k => ψ x)) (hu : ∀ x : k, ‖ψ x‖ = 1)
    (hn : ∃ x : k, ψ x ≠ 1) (d : k) (hd : d ≠ 0) (a : kˣ) :
    (QuadraticNormCharacter.normSign d a : ℂ) * (Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 2 * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d)) =
      Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (2 * a.val) * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-2 * d * a.val) := by
  have h2 : (2 : k) ≠ 0 := by norm_num
  have hmd : -2 * d ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) hd
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    rcases NormedField.discreteTopology_or_nontriviallyNormedField k with h | ⟨_, rfl⟩
    · exact (hnd h).elim
    · exact NonarchimedeanNormGaussian.norm_character_gaussian_identity d hd hnd ψ hc hu hn a
  · rcases Weil.Local.ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, he'⟩ | ⟨e, he, he'⟩
    · obtain ⟨s, hs, _, hNorm⟩ := Weil.Local.ArchimedeanNorm.Construction.continuous_real_embedding_norm_power hArch e.symm.toRingHom he'
      obtain ⟨c, hcz, hψ⟩ := Weil.Local.RealCharacters.Construction.continuous_nontrivial_unitary_real_character (Weil.Local.FieldFourier.Construction.fieldCharacter e ψ)
        (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_continuous e he' ψ hc) (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_unitary e ψ hu)
        (Weil.Local.ArchimedeanKernel.Construction.fieldCharacter_nontrivial e ψ hn)
      have hγ := Weil.Local.RealFieldEq.Construction.gaussianIndex_realField_eq e he he' ψ c s hψ hNorm hs hcz
      rw [hγ 2 h2, hγ (-2 * d) hmd, hγ (2 * a.val) (mul_ne_zero h2 a.ne_zero),
        hγ (-2 * d * a.val) (mul_ne_zero hmd a.ne_zero), ← QuadraticNormTransport.normSign_map e d a]
      simpa only [map_mul, map_neg, map_ofNat, Units.coe_map,
        show e.toMonoidHom a.val = e a.val from rfl] using
        RealNormGaussian.norm_character_gaussian_identity (e d) ((map_ne_zero e).mpr hd)
          c hcz (Units.map e.toMonoidHom a)
    · have hsq : IsSquare d := by
        refine ⟨e.symm ((e d) ^ (1 / 2 : ℂ)), ?_⟩
        apply e.injective
        simp only [map_mul, e.apply_symm_apply]
        rw [← pow_two]
        simp [one_div]
      have hγ := Weil.Local.ComplexFieldGaussian.Construction.complexField_gaussian_normalization hArch e he he' ψ hc hu hn
      rw [QuadraticNormCharacter.normSign_split d hd hsq a, Circle.coe_one, (hγ 2 h2).2.2,
        (hγ (-2 * d) hmd).2.2, (hγ (2 * a.val) (mul_ne_zero h2 a.ne_zero)).2.2,
        (hγ (-2 * d * a.val) (mul_ne_zero hmd a.ne_zero)).2.2, one_mul, one_mul]

end

end OAI.RepresentationTheory.Theta.Adelic.LocalNormGaussian
