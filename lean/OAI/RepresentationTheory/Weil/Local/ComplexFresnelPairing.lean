import OAI.RepresentationTheory.Weil.Local.ComplexFresnelGaussian
import OAI.RepresentationTheory.Weil.Local.FresnelLimit

/-! # Complex Fresnel Pairing -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFresnelPairing.Construction

noncomputable section

/-! The standard complex Fresnel pairing has coefficient one. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

def complexTensorDamping (n : ℕ) (ε : ℝ) (x : FunctionsMetaplectic.Construction.Position ℂ n) : ℂ :=
  ∏ i, ComplexFresnelGaussian.Construction.complexQuadraticDamping ε (x i)

theorem complexTensorDamping_integrable (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (complexTensorDamping n ε) :=
  Integrable.fintype_prod (fun _ => ComplexFresnelGaussian.Construction.complexQuadraticDamping_integrable ε hε)

theorem complexTensorDamping_tendsto {n : ℕ} (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    Tendsto (fun ε => complexTensorDamping n ε x) (𝓝[>] (0 : ℝ))
      (𝓝 (ArchimedeanTestSpace.Construction.complexStandardCharacter (FunctionsMetaplectic.Construction.quadratic 1 x))) := by
  have h := tendsto_finsetProd Finset.univ (fun (i : Fin n) _ => ComplexFresnelGaussian.Construction.complexQuadraticDamping_tendsto (x i))
  simpa only [complexTensorDamping, ← CompactCharacter.Construction.character_finset_sum, ← FresnelLimit.Construction.quadratic_one_sum] using! h

theorem fourier_complexTensorDamping {n : ℕ} (ε : ℝ) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (complexTensorDamping n ε) x =
      ∏ i, FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (ComplexFresnelGaussian.Construction.complexQuadraticDamping ε) (x i) :=
  FourierTensor.Construction.fourierIntegral_product ArchimedeanTestSpace.Construction.complexStandardCharacter volume (fun _ => ComplexFresnelGaussian.Construction.complexQuadraticDamping ε) x

theorem fourier_complexTensorDamping_tendsto {n : ℕ} (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    Tendsto (fun ε => FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (complexTensorDamping n ε) x)
      (𝓝[>] (0 : ℝ)) (𝓝 (ArchimedeanTestSpace.Construction.complexStandardCharacter (-FunctionsMetaplectic.Construction.quadratic 1 x))) := by
  simp_rw [fourier_complexTensorDamping]
  have h := tendsto_finsetProd Finset.univ
    (fun (i : Fin n) _ => ComplexFresnelGaussian.Construction.scalarFourier_complexQuadraticDamping_tendsto (x i))
  simpa only [← CompactCharacter.Construction.character_finset_sum, Finset.sum_neg_distrib, ← FresnelLimit.Construction.quadratic_one_sum] using! h

theorem complex_fresnel_pairing_standard {n : ℕ} (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume f.val x * ArchimedeanTestSpace.Construction.complexStandardCharacter (FunctionsMetaplectic.Construction.quadratic 1 x)) =
      ∫ x, f.val x * ArchimedeanTestSpace.Construction.complexStandardCharacter (-FunctionsMetaplectic.Construction.quadratic 1 x) := by
  have hχ : Continuous (fun z => ArchimedeanTestSpace.Construction.complexStandardCharacter z) :=
    (RealTestSpace.Construction.realCharacter_temperate 1).1.continuous.comp Complex.continuous_re
  have hu : ∀ z, ‖ArchimedeanTestSpace.Construction.complexStandardCharacter z‖ = 1 := fun z => QuadraticIntertwiner.Construction.realCharacter_unitary 1 z.re
  have hg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Integrable (complexTensorDamping n ε) := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
    exact complexTensorDamping_integrable n ε hε
  have hgb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, ‖complexTensorDamping n ε x‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε x
    rw [complexTensorDamping, norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun i _ => ComplexFresnelGaussian.Construction.complexQuadraticDamping_norm_le ε hε.le (x i))
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖Gaussian.Construction.realDampedGaussian 1 1 ε * Gaussian.Construction.realDampedGaussian (-1) 1 ε‖ ≤ 2 := by
    have h := ComplexFresnelGaussian.Construction.realDampedGaussian_opposite_product_tendsto.norm.eventually_le_const (by norm_num : ‖(1 : ℂ)‖ < 2)
    exact h
  have hFb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x,
      ‖FunctionsMetaplectic.Construction.fourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (complexTensorDamping n ε) x‖ ≤ 2 ^ n := by
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0), hb] with ε hε hεb x
    rw [fourier_complexTensorDamping, norm_prod]
    calc
      _ ≤ ∏ _ : Fin n, (2 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => (ComplexFresnelGaussian.Construction.scalarFourier_complexQuadraticDamping_norm_le ε hε (x i)).trans hεb)
      _ = _ := by simp
  have h := FresnelLimit.Construction.fresnel_pairing_of_dominated_cutoffs ArchimedeanTestSpace.Construction.complexStandardCharacter hu hχ volume
    (complexTensorDamping n) 1 (2 ^ n) hg hgb complexTensorDamping_tendsto hFb
    (fun x => by simpa only [one_mul] using fourier_complexTensorDamping_tendsto x)
    (FunctionsMetaplectic.Construction.schwartzBruhat_integrable volume f)
    (FunctionsMetaplectic.Construction.schwartzBruhat_integrable volume ⟨_, ComplexStandardNormalization.Construction.complex_fourier_mem_standard n f⟩)
  simpa only [one_mul] using h

end

end OAI.RepresentationTheory.Weil.Local.ComplexFresnelPairing.Construction
