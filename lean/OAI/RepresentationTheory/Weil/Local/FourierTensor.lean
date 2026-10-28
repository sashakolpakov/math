import OAI.RepresentationTheory.Weil.Local.NonarchimedeanHaar
import Mathlib.MeasureTheory.Integral.Pi

/-! # Fourier Tensor -/

namespace OAI.RepresentationTheory.Weil.Local.FourierTensor.Construction

noncomputable section

section

/-! Product Fourier integrals and the dimension dependence of the local normalization. -/

open _root_.MeasureTheory
open scoped Classical

def scalarFourierIntegral
    {k : Type} [Field k] [MeasurableSpace k]
    (ψ : AddChar k ℂ) (μ : Measure k) (f : k → ℂ) (x : k) : ℂ :=
  ∫ y, f y * ψ (-(x * y)) ∂μ

theorem fourierIntegral_product
    {k : Type} [NormedField k] [MeasurableSpace k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [SigmaFinite μ]
    (f : Fin n → k → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (fun y => ∏ i, f i (y i)) x =
      ∏ i, scalarFourierIntegral ψ μ (f i) (x i) := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral scalarFourierIntegral
  rw [← integral_fintype_prod_eq_prod]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.dot, ← Finset.sum_neg_distrib, CompactCharacter.Construction.character_finset_sum, Finset.prod_mul_distrib]

theorem scalarFourier_square_reference
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    {f : k → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) (x : k) :
    scalarFourierIntegral ψ Measure.addHaar (scalarFourierIntegral ψ Measure.addHaar f) x =
      (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) * f (-x) := by
  let f₁ : FunctionsMetaplectic.Construction.Position k 1 → ℂ := fun y => f (y 0)
  have hf₁ : IsLocallyConstant f₁ := hf.comp_continuous (continuous_apply 0)
  have hs₁ : HasCompactSupport f₁ := hs.comp_homeomorph (Homeomorph.funUnique (Fin 1) k)
  have heq : FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k))) f₁ =
      fun y => scalarFourierIntegral ψ Measure.addHaar f (y 0) :=
    funext (NonarchimedeanHaar.Construction.fourierIntegral_singleton_position ψ Measure.addHaar f)
  have h := (NonarchimedeanHaar.Construction.nonarchimedean_reference_scale hNondiscrete ψ hu hc hn).2 f₁ hf₁ hs₁ (fun _ => x)
  rw [heq, NonarchimedeanHaar.Construction.fourierIntegral_singleton_position] at h
  exact h

theorem unitBall_indicator_product
    {k : Type} [NormedField k] {n : ℕ} (x : FunctionsMetaplectic.Construction.Position k n) :
    (Metric.closedBall (0 : FunctionsMetaplectic.Construction.Position k n) 1).indicator (fun _ => (1 : ℂ)) x =
      ∏ i, (Metric.closedBall (0 : k) 1).indicator (fun _ => (1 : ℂ)) (x i) := by
  have hmem : x ∈ Metric.closedBall (0 : FunctionsMetaplectic.Construction.Position k n) 1 ↔
      ∀ i, x i ∈ Metric.closedBall (0 : k) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact pi_norm_le_iff_of_nonneg zero_le_one
  by_cases hx : x ∈ Metric.closedBall (0 : FunctionsMetaplectic.Construction.Position k n) 1
  · rw [Set.indicator_of_mem hx]
    symm
    exact Finset.prod_eq_one (fun i _ => Set.indicator_of_mem (hmem.mp hx i) _)
  · rw [Set.indicator_of_notMem hx]
    have hx' : ¬ ∀ i, x i ∈ Metric.closedBall (0 : k) 1 := fun h => hx (hmem.mpr h)
    push Not at hx'
    obtain ⟨i, hi⟩ := hx'
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem nonarchimedean_fourier_square_reference
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k)))
      (FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))) f) x =
        ((FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) ^ n) * f (-x) := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ : Measure k := Measure.addHaar
  let μn : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => μ)
  let : μn.IsAddHaarMeasure := by dsimp [μn, μ]; infer_instance
  obtain ⟨c, _, hsquare⟩ := NonarchimedeanFourier.Construction.nonarchimedean_fourier_square_positive_scalar hNondiscrete n ψ hu hc hn μn
  let U := IsUltrametricDist.closedBall_openAddSubgroup k zero_lt_one
  let Un := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) zero_lt_one
  let b : k → ℂ := (U : Set k).indicator (fun _ => 1)
  let bn : FunctionsMetaplectic.Construction.Position k n → ℂ := (Un : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1)
  have hb : IsLocallyConstant b := CompactCharacter.Construction.subgroup_indicator_locallyConstant U
  have hsb : HasCompactSupport b := CompactCharacter.Construction.subgroup_indicator_compactSupport U (isCompact_closedBall 0 1)
  have hbn : IsLocallyConstant bn := CompactCharacter.Construction.subgroup_indicator_locallyConstant Un
  have hsbn : HasCompactSupport bn := CompactCharacter.Construction.subgroup_indicator_compactSupport Un (isCompact_closedBall 0 1)
  have hprod : bn = fun y => ∏ i, b (y i) := funext unitBall_indicator_product
  have hF : FunctionsMetaplectic.Construction.fourierIntegral ψ μn bn = fun y => ∏ i, scalarFourierIntegral ψ μ b (y i) := by
    rw [hprod]
    exact funext (fourierIntegral_product ψ μ (fun _ => b))
  have hFF : FunctionsMetaplectic.Construction.fourierIntegral ψ μn (FunctionsMetaplectic.Construction.fourierIntegral ψ μn bn) 0 =
      (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) ^ n := by
    rw [hF, fourierIntegral_product]
    dsimp only [μ]
    simp only [Pi.zero_apply, scalarFourier_square_reference hNondiscrete ψ hu hc hn hb hsb,
      neg_zero, show b 0 = 1 by simp [b], mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : (c : ℂ) = (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) ^ n := by
    have h := hsquare bn hbn hsbn 0
    rw [hFF] at h
    simpa [bn] using h.symm
  rw [hsquare f hf hs, hc]

end

/-! Compact pure tensors for calibrating Fourier normalization. -/

open _root_.MeasureTheory
open scoped Classical

def tensorFunction {k : Type} (n : ℕ) (f : k → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) : ℂ :=
  ∏ i, f (x i)

theorem tensorFunction_compactSupport {k : Type} [TopologicalSpace k] [T2Space k]
    (n : ℕ) {f : k → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (tensorFunction n f) := by
  apply HasCompactSupport.intro (isCompact_pi_infinite fun _ : Fin n => hf)
  intro x hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  have hz : f (x i) = 0 := image_eq_zero_of_notMem_tsupport hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

theorem fourierIntegral_tensorFunction
    {k : Type} [NormedField k] [MeasurableSpace k] (n : ℕ)
    (ψ : AddChar k ℂ) (μ : Measure k) [SigmaFinite μ] (f : k → ℂ) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (tensorFunction n f) =
      tensorFunction n (scalarFourierIntegral ψ μ f) :=
  funext (fourierIntegral_product ψ μ (fun _ => f))

end

end OAI.RepresentationTheory.Weil.Local.FourierTensor.Construction
