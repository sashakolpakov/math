import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Fourier Tools -/

namespace OAI.RepresentationTheory.Weil.Local.FourierTools.Construction

noncomputable section

/-! Fourier integrals on the concrete local Bruhat space. -/

open _root_.MeasureTheory
open scoped BigOperators ENNReal

def circleCharacter {k : Type} [Field k]
    (ψ : AddChar k ℂ) (hψ : ∀ t : k, ‖ψ t‖ = 1) : AddChar k Circle where
  toFun t := ⟨ψ t, mem_sphere_zero_iff_norm.mpr (hψ t)⟩
  map_zero_eq_one' := Subtype.ext ψ.map_zero_eq_one
  map_add_eq_mul' x y := Subtype.ext (ψ.map_add_eq_mul x y)

theorem circleCharacter_continuous {k : Type} [NormedField k]
    (ψ : AddChar k ℂ) (hψ : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) : Continuous (circleCharacter ψ hψ) :=
  hc.subtype_mk _

theorem dot_comm {k : Type} [CommSemiring k] {n : ℕ} (x y : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.dot x y = FunctionsMetaplectic.Construction.dot y x := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem dotProductBilin_continuous {k : Type} [NormedField k] (n : ℕ) :
    Continuous (fun p : FunctionsMetaplectic.Construction.Position k n × FunctionsMetaplectic.Construction.Position k n => dotProductBilin k k p.1 p.2) := by
  change Continuous (fun p : FunctionsMetaplectic.Construction.Position k n × FunctionsMetaplectic.Construction.Position k n => ∑ i, p.1 i * p.2 i)
  fun_prop

theorem fourierIntegral_eq_vectorFourier
    {k : Type} [Field k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : ∀ t : k, ‖ψ t‖ = 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ f =
      VectorFourier.fourierIntegral (circleCharacter ψ hψ) μ (dotProductBilin k k) f := by
  funext x
  unfold FunctionsMetaplectic.Construction.fourierIntegral VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with y
  change f y * ψ (-FunctionsMetaplectic.Construction.dot x y) = ψ (-FunctionsMetaplectic.Construction.dot y x) * f y
  rw [dot_comm x y, mul_comm]

theorem fourierKernel_integrable
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (μ : Measure (FunctionsMetaplectic.Construction.Position k n))
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ) (x : FunctionsMetaplectic.Construction.Position k n) :
    Integrable (fun y => f y * ψ (-FunctionsMetaplectic.Construction.dot x y)) μ := by
  have hp : Continuous (fun y : FunctionsMetaplectic.Construction.Position k n => ψ (-FunctionsMetaplectic.Construction.dot x y)) := by
    apply hc.comp
    unfold FunctionsMetaplectic.Construction.dot
    fun_prop
  apply hf.norm.mono (hf.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  filter_upwards with y
  simp only [Pi.mul_apply, norm_mul, hψ, mul_one, norm_norm, le_refl]

theorem fourierIntegral_continuous
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hψ : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (μ : Measure (FunctionsMetaplectic.Construction.Position k n))
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ) :
    Continuous (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  rw [fourierIntegral_eq_vectorFourier ψ hψ]
  exact VectorFourier.fourierIntegral_continuous
    (circleCharacter_continuous ψ hψ hc) (dotProductBilin_continuous n) hf

def schwartzBruhat_fourierLinearMap
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] (n : ℕ)
    (ψ : AddChar k ℂ) (hψ : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    FunctionsMetaplectic.Construction.schwartzBruhat k n →ₗ[ℂ] (FunctionsMetaplectic.Construction.Position k n → ℂ) where
  toFun f := FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val
  map_add' f g := by
    funext x
    exact FunctionsMetaplectic.Construction.fourierIntegral_add ψ μ f.val g.val x
      (fourierKernel_integrable ψ hψ hc μ (FunctionsMetaplectic.Construction.schwartzBruhat_integrable μ f) x)
      (fourierKernel_integrable ψ hψ hc μ (FunctionsMetaplectic.Construction.schwartzBruhat_integrable μ g) x)
  map_smul' c f := FunctionsMetaplectic.Construction.fourierIntegral_smul ψ μ c f.val

theorem selfDualMeasure_isAddHaarMeasure_of_scale_pos
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k ℂ) (h : 0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ) :
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure := by
  apply Measure.IsAddHaarMeasure.smul
  · exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr (Real.sqrt_pos.mpr h))).ne'
  · exact ENNReal.ofReal_ne_top

end

end OAI.RepresentationTheory.Weil.Local.FourierTools.Construction
