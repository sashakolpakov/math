import OAI.RepresentationTheory.Weil.Local.ComplexFieldNormalization
import OAI.RepresentationTheory.Weil.Local.ComplexFieldGaussian
import OAI.RepresentationTheory.Weil.Local.ComplexCover
import OAI.RepresentationTheory.Weil.Local.FieldFourier

/-! # Complex Field Analytic -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFieldAnalytic.Construction

noncomputable section

/-! All analytic clauses of LocalWeil for an arbitrary complex topological field presentation. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem complexField_fourier_inversion
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1)
    (hn : ∃ t, ψ t ≠ 1) (n : ℕ) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val) x = f.val (-x) := by
  let η := FieldFourier.Construction.fieldCharacter e ψ
  have hηc : Continuous (fun t => η t) := hc.comp he'
  have hηu : ∀ t, ‖η t‖ = 1 := fun t => hu (e.symm t)
  have hηn : ∃ t, η t ≠ 1 := by
    obtain ⟨t, ht⟩ := hn
    refine ⟨e t, ?_⟩
    change ψ (e.symm (e t)) ≠ 1
    rwa [e.symm_apply_apply]
  have ha := ComplexCover.Construction.complex_analytic_normalization η hηc hηu hηn n
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℂ η).IsAddHaarMeasure := ha.2.1
  have hmap := (ComplexFieldNormalization.Construction.complexField_selfDual_normalization e he he' ψ hc hu hn).2.2
  have hF (g : FunctionsMetaplectic.Construction.Position k n → ℂ) (y : FunctionsMetaplectic.Construction.Position ℂ n) :
      FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℂ n η) (fun z => g (fun i => e.symm (z i))) y =
        FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) g (fun i => e.symm (y i)) :=
    FieldFourier.Construction.field_fourierIntegral e he he' (FunctionsMetaplectic.Construction.selfDualMeasure k ψ) (FunctionsMetaplectic.Construction.selfDualMeasure ℂ η) hmap n ψ g y
  have hinner : FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℂ n η)
      (fun y => f.val (fun i => e.symm (y i))) =
    fun y => FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val (fun i => e.symm (y i)) :=
      funext (hF f.val)
  let C := FieldCoordinates.Construction.testSpaceTransport (FieldCoordinates.Construction.fieldPositionEquiv e he he' n)
  have hh := ha.2.2.2 (C f) (fun i => e (x i))
  change FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℂ n η)
      (FunctionsMetaplectic.Construction.fourierIntegral η (FunctionsMetaplectic.Construction.positionMeasure ℂ n η) (fun y => f.val (fun i => e.symm (y i))))
      (fun i => e (x i)) = f.val (fun i => e.symm (-e (x i))) at hh
  rw [hinner, hF] at hh
  simpa only [RingEquiv.symm_apply_apply, map_neg] using! hh

theorem complexField_analytic_normalization
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (hArch : ¬ ∀ m : ℕ, ‖(m : k)‖ ≤ 1)
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
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
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  have hμ := ComplexFieldNormalization.Construction.complexField_selfDual_normalization e he he' ψ hc hu hn
  exact ⟨hμ.1, hμ.2.1,
    fun a ha => by
      have hg := ComplexFieldGaussian.Construction.complexField_gaussian_normalization hArch e he he' ψ hc hu hn a ha
      exact ⟨hg.1, hg.2.1, by rw [hg.2.2, one_pow]⟩,
    complexField_fourier_inversion e he he' ψ hc hu hn n⟩

end

end OAI.RepresentationTheory.Weil.Local.ComplexFieldAnalytic.Construction
