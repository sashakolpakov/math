import OAI.RepresentationTheory.Weil.Local.ComplexNormalization
import OAI.RepresentationTheory.Weil.Local.FourierEquivalence
import OAI.RepresentationTheory.Weil.Local.RealCover

/-! # Complex Cover -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexCover.Construction

noncomputable section

/-! Full complex analytic normalization and surjectivity of the intrinsic bare cover. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem complex_analytic_normalization
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) (n : ℕ) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℂ ψ ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure ∧
    (∀ a : ℂ, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℂ ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral ℂ ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral ℂ ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ a ^ 8 = 1) ∧
    (∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val) x = f.val (-x)) := by
  have h := ComplexNormalization.Construction.complex_fourier_analysis n ψ hc hu hn
  refine ⟨h.1, FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ h.1, ?_, h.2.2⟩
  intro a ha
  obtain ⟨hlim, hnz, hγ⟩ := ArchimedeanTestSpace.Construction.complex_gaussian_normalization ψ hc hu hn a ha
  exact ⟨hlim, hnz, by rw [hγ, one_pow]⟩

def complexRawFourierOscillator (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    FunctionsMetaplectic.Construction.Oscillator ℂ n ψ := by
  have h := ComplexNormalization.Construction.complex_fourier_analysis n ψ hc hu hn
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure :=
    FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℂ ψ h.1
  let : (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ).IsAddHaarMeasure := by unfold FunctionsMetaplectic.Construction.positionMeasure; infer_instance
  exact FourierEquivalence.Construction.fourierOscillator ψ hu hc (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) h.2.1 h.2.2

theorem complexRawFourierOscillator_apply (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    ((complexRawFourierOscillator n ψ hc hu hn).val.2 f).val x =
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val x := rfl

theorem complex_metaplecticProjection_surjective (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    Function.Surjective (FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ) := by
  let w := complexRawFourierOscillator n ψ hc hu hn
  have hw : OscillatorProjection.Construction.oscillatorProjection ℂ n ψ w = Generators.Construction.weylSymplectic ℂ n := rfl
  apply MonoidHom.range_eq_top.mp
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu ⟨-B.val, B.property.neg⟩
    have h : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ := by
      have hh := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ).Normal).conj_mem u.val u.property w⁻¹
      simpa only [inv_inv] using hh
    refine ⟨⟨w⁻¹ * u.val * w, h⟩, ?_⟩
    change OscillatorProjection.Construction.oscillatorProjection ℂ n ψ (w⁻¹ * u.val * w) = GenerationSymplectic.Construction.upperSymplectic B
    rw [map_mul, map_mul, map_inv, hw]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℂ n B).symm
  · intro B
    exact ⟨ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu B, rfl⟩

end

end OAI.RepresentationTheory.Weil.Local.ComplexCover.Construction
