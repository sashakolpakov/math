import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactApproximation
import OAI.RepresentationTheory.Weil.AdelicSplitting.OneCoordinate

/-! # Nonarchimedean Reference -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanReference.LocalAnalysis

noncomputable section

/-! Plancherel for arbitrary compact indicators, including the reference
compact set used to define self-dual Haar measure. -/

open _root_.MeasureTheory
open scoped ENNReal

variable {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
  [MeasurableSpace k] [BorelSpace k] [ProperSpace k] [SecondCountableTopology k]
  [NonarchimedeanAddGroup k]

theorem nonarchimedean_fourier_analysis_scalar (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      (∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) x,
        Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = (c : ℂ) * f.val (-x)) ∧
      ∀ (S : Set (Local.FunctionsMetaplectic.Construction.Position k n)), IsCompact S →
        MemLp (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (S.indicator (fun _ => (1 : ℂ)))) 2 μ ∧
        (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (S.indicator (fun _ => (1 : ℂ))) x‖ ^ 2 ∂μ) = c * μ.real S := by
  obtain ⟨c, hcpos, hSquare⟩ := FourierCompactDomain.LocalAnalysis.nonarchimedean_fourier_square_scalar n ψ hu hc hn μ
  have hStable := NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_fourier_mem ψ hu hc hn μ
  have hEnergy := NonarchimedeanFourier.LocalAnalysis.fourierIntegral_scaled_norm_sq ψ hu hc μ hStable c hSquare
  refine ⟨c, hcpos, hSquare, ?_⟩
  intro S hS
  let f : ℕ → Local.FunctionsMetaplectic.Construction.schwartzBruhat k n := fun j =>
    ⟨(CompactApproximation.LocalAnalysis.compactNeighborhood S j).indicator (fun _ => (1 : ℂ)),
      Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem
        (LocallyConstant.charFn ℂ (CompactApproximation.LocalAnalysis.compactNeighborhood_clopen hS j)).isLocallyConstant
        (HasCompactSupport.intro (CompactApproximation.LocalAnalysis.compactNeighborhood_compact hS j)
          (fun x hx => Set.indicator_of_notMem hx _))⟩
  let g : Local.FunctionsMetaplectic.Construction.Position k n → ℂ := S.indicator (fun _ => 1)
  have hg (p : ℝ≥0∞) : MemLp g p μ :=
    memLp_indicator_const p hS.measurableSet 1 (Or.inr hS.measure_ne_top)
  have h := NonarchimedeanFourier.LocalAnalysis.fourier_L2_limit ψ hu hc μ hStable c hcpos hEnergy f g
    (memLp_one_iff_integrable.mp (hg 1)) (hg 2)
    (CompactApproximation.LocalAnalysis.compactNeighborhood_indicator_eLpNorm_tendsto μ hS 1 (by norm_num) (by norm_num))
    (CompactApproximation.LocalAnalysis.compactNeighborhood_indicator_eLpNorm_tendsto μ hS 2 (by norm_num) (by norm_num))
  refine ⟨h.1, h.2.trans ?_⟩
  congr 1
  have he : (fun x => ‖g x‖ ^ 2) = S.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [g, hx]
  rw [he]
  exact integral_indicator_one hS.measurableSet

theorem nonarchimedean_one_coordinate_normalization
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (hn : ∃ t, ψ t ≠ 1) :
    0 < Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ∧
    ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k 1) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k)))
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k))) f.val) x =
          (Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) * f.val (-x) := by
  let μ : Measure (Local.FunctionsMetaplectic.Construction.Position k 1) := Measure.pi (fun _ : Fin 1 => (Measure.addHaar : Measure k))
  obtain ⟨c, hcpos, hSquare, hPlancherel⟩ := nonarchimedean_fourier_analysis_scalar 1 ψ hu hc hn μ
  let S : Set (Local.FunctionsMetaplectic.Construction.Position k 1) := {x | x 0 ∈ (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k)}
  have hS : IsCompact S := OneCoordinate.LocalAnalysis.compact_one_coordinate (Local.FunctionsMetaplectic.Construction.referenceCompact k).isCompact
  have hm : μ.real S = (Measure.addHaar : Measure k).real (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) := by
    rw [measureReal_def, measureReal_def]
    congr 1
    exact OneCoordinate.LocalAnalysis.measure_one_coordinate (Measure.addHaar : Measure k) (Local.FunctionsMetaplectic.Construction.referenceCompact k).isCompact.measurableSet
  have hF := (hPlancherel S hS).2
  simp only [S, μ, OneCoordinate.LocalAnalysis.referenceFourier_one_coordinate] at hF
  have hField : (∫ x, ‖Local.FunctionsMetaplectic.Construction.referenceFourier k ψ x‖ ^ 2 ∂(Measure.addHaar : Measure k)) =
      c * μ.real S := (OneCoordinate.LocalAnalysis.integral_one_coordinate (Measure.addHaar : Measure k)
        (fun x => ‖Local.FunctionsMetaplectic.Construction.referenceFourier k ψ x‖ ^ 2)).symm.trans hF
  rw [hm] at hField
  have hpos : 0 < (Measure.addHaar : Measure k).real (Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) := by
    apply ENNReal.toReal_pos
    · exact (Measure.measure_pos_of_nonempty_interior (Measure.addHaar : Measure k)
        (Local.FunctionsMetaplectic.Construction.referenceCompact k).interior_nonempty).ne'
    · exact (Local.FunctionsMetaplectic.Construction.referenceCompact k).isCompact.measure_ne_top
  have he : Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ = c := by
    rw [Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared, hField]
    exact mul_div_cancel_right₀ _ hpos.ne'
  rw [he]
  exact ⟨hcpos, hSquare⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanReference.LocalAnalysis
