import OAI.RepresentationTheory.Theta.Adelic.LocalNormGaussian
import OAI.RepresentationTheory.Theta.Adelic.RationalFourier

/-! # Norm Character Reciprocity -/

namespace OAI.RepresentationTheory.Theta.Adelic.NormCharacterReciprocity

noncomputable section

/-! Quadratic norm reciprocity follows from the four actual adelic Gaussian
products, independently of any supplied unitary splitting. -/

open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormCharacter OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial

theorem normCharacter_principal_hasProd
    (F : Type) [Field F] [NumberField F] (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) (hn : ∃ x, ψ x ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (d : F) (hd : d ≠ 0) (a : Fˣ) :
    HasProd (fun v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F => (Weil.AdelicSplitting.Characters.Construction.normCharacter F d v
      (Units.map (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom a) : ℂ)) 1 := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hmd : -2 * d ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) hd
  let γ := fun (b : F) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) => Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)
    (Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v b)
  have hγ (b : F) (hb : b ≠ 0) : HasProd (γ b) 1 :=
    RationalFourier.gaussianIndex_principal_hasProd F ψ hc hu hn hp b hb
  have hloc (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
      (Weil.AdelicSplitting.Characters.Construction.normCharacter F d v (Units.map (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom a) : ℂ) =
        (γ (2 * a.val) v * γ (-2 * d * a.val) v) / (γ 2 v * γ (-2 * d) v) := by
    let f := Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v
    let ψv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v
    have hcv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_continuous F ψ hc v
    have huv := Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter_unitary F ψ hu v
    have hnv := FiniteCharacterNontrivial.local_character_nontrivial F ψ hc hu hn hp v
    have hga (b : F) (hb : b ≠ 0) : γ b v ≠ 0 :=
      Weil.Local.FunctionsMetaplectic.Construction.phase_ne_zero ((Weil.Local.Analytic.Construction.localField_analytic_normalization (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F v)
        ψv hcv huv hnv 1).2.2.1 (f b) ((map_ne_zero f).mpr hb)).2.1
    apply (eq_div_iff (mul_ne_zero (hga 2 h2) (hga (-2 * d) hmd))).mpr
    have h := LocalNormGaussian.norm_character_gaussian_identity
      (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F v) ψv hcv huv hnv (f d) ((map_ne_zero f).mpr hd)
      (Units.map f.toMonoidHom a)
    have hva : (Units.map f.toMonoidHom a).val = f a.val := rfl
    rw [hva] at h
    simpa only [γ, ψv, f, map_mul, map_neg, map_ofNat, ← QuadraticNormCharacter.normSign_eq_normCharacter] using h
  have hprod := ((hγ (2 * a.val) (mul_ne_zero h2 a.ne_zero)).mul
    (hγ (-2 * d * a.val) (mul_ne_zero hmd a.ne_zero))).div₀
      ((hγ 2 h2).mul (hγ (-2 * d) hmd)) (by norm_num)
  simpa only [one_mul, one_div, inv_one] using hprod.congr_fun hloc

end

end OAI.RepresentationTheory.Theta.Adelic.NormCharacterReciprocity
