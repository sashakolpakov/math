import OAI.RepresentationTheory.Weil.Local.RealFieldAnalytic
import OAI.RepresentationTheory.Weil.Local.ComplexFieldAnalytic
import OAI.RepresentationTheory.Weil.Local.GaussianNonarchimedean
import Mathlib.Analysis.Normed.Field.Ultra

/-! # Analytic -/

namespace OAI.RepresentationTheory.Weil.Local.Analytic.Construction

noncomputable section

/-! Actual Haar, Gaussian and Fourier normalization under the natural LocalWeil local-field hypotheses. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem localField_analytic_normalization
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (n : ℕ) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure ∧
    (∀ a : k, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex k ψ a ^ 8 = 1) ∧
    (∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val) x = f.val (-x)) := by
  by_cases hArch : ∀ m : ℕ, ‖(m : k)‖ ≤ 1
  · let : IsUltrametricDist k :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one hArch
    exact GaussianNonarchimedean.Construction.nonarchimedean_analytic_normalization hNondiscrete ψ hu hc hn n
  · rcases ArchimedeanClassification.Construction.localField_archimedean_classification k hArch with ⟨e, he, he'⟩ | ⟨e, he, he'⟩
    · exact RealFieldAnalytic.Construction.realField_analytic_normalization hNondiscrete hArch e he he' ψ hc hu hn n
    · exact ComplexFieldAnalytic.Construction.complexField_analytic_normalization hNondiscrete hArch e he he' ψ hc hu hn n

end

end OAI.RepresentationTheory.Weil.Local.Analytic.Construction
